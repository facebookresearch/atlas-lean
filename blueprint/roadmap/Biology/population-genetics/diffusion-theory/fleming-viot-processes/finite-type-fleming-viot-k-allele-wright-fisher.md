# Finite-type Fleming–Viot and Wright–Fisher martingale problems

Let $E=\{1,\ldots,d\}$ with $d\ge1$. Let $Q=(q_{ab})$ be a finite mutation rate matrix, with nonnegative off-diagonal entries and zero row sums. In the lookdown notation, $Q=\frac\theta2(P-I)$, where $P$ is stochastic and $\theta\ge0$; conversely every finite rate matrix has such a representation, taking $\theta/2\ge\max_a(-q_{aa})$ and handling $Q=0$ separately. Identify a probability measure on $E$ with its mass vector $z\in\Delta_{d-1}$.

For $f:E^m\to\mathbb R$, put $F_f(z)=\langle f,z^{\otimes m}\rangle$. Define the finite-type Fleming–Viot polynomial operator by

$$\mathcal A F_f(z)=\sum_{r=1}^m\langle B_rf,z^{\otimes m}\rangle+\sum_{1\le r<s\le m}\langle\Phi_{rs}f-f,z^{\otimes m}\rangle,$$

where $B$ has matrix $Q$, and $\Phi_{rs}$ overwrites input $s$ with input $r$. Then this operator is well-defined on polynomial functions restricted to the simplex and equals the no-selection [multi-allele Wright–Fisher generator](../wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md):

$$L\varphi(z)=\frac12\sum_{a,b=1}^d z_a(\delta_{ab}-z_b)\,\partial_a\partial_b\varphi(z)+\sum_{b=1}^d\left(\sum_{a=1}^d z_aq_{ab}\right)\partial_b\varphi(z).$$

The measure-to-mass-vector homeomorphism gives a bijection between solution laws of the polynomial Fleming–Viot martingale problem and the Wright–Fisher martingale problem on $C^2$ test functions defined on a neighborhood of the simplex, with corresponding initial laws and the same path class on both sides (continuous, or càdlàg). This is an operator and solution-class correspondence, not a proof of existence, uniqueness, or continuity of every càdlàg solution. For $d=1$ both operators vanish on the one-point simplex.

## Polynomial computation and test-function class

For a multi-index $\mathbf n\in\mathbb N_0^d$, write $m=\sum_a n_a$ and $\varphi_{\mathbf n}(z)=\prod_a z_a^{n_a}$. Choose the cylinder indicator requiring $n_a$ sampled inputs to equal type $a$. Its mutation contribution is

$$\sum_{b:n_b\ge1} n_b\sum_a q_{ab}z_a\,\varphi_{\mathbf n-e_b}(z),$$

and its reproduction contribution is

$$\sum_{a:n_a\ge2}\binom{n_a}{2}\varphi_{\mathbf n-e_a}(z)-\binom m2\varphi_{\mathbf n}(z).$$

These are precisely the first- and second-order parts of $L\varphi_{\mathbf n}$. The restricted sums avoid undefined negative exponents, including on boundary faces. Constants ($m=0$) have generator zero. Cylinder indicators span every finite-input $f$, so linearity gives the full polynomial identity. Drift and covariance are tangent to the simplex, so the operator depends only on the restricted polynomial, not its ambient representation.

For a $C^2$ function on a neighborhood of the simplex, first extend it to a $C^2$ function on a box, agreeing near the simplex. Approximate it there by polynomials together with every partial derivative of order at most two, uniformly. Boundedness of the generator coefficients on the simplex then gives uniform convergence of both test functions and generators. Dominated convergence in the bounded-time martingale identities extends the polynomial problem to this $C^2$ class. Uniform approximation of function values alone is not enough. Conversely, the $C^2$ class contains every polynomial.

## Parent-independent mutation and merging types

For parent-independent mutation to a probability vector $\nu$, take $p_{ab}=\nu_b$, including self draws. Then

$$\sum_a z_aq_{ab}=\frac\theta2(\nu_b-z_b).$$

For two types, with $x=z_1$, the convention is $\theta_1=\theta\nu_1$ and $\theta_2=\theta\nu_2$, giving drift $\frac12[\theta_1(1-x)-\theta_2x]$. The resampling coefficient remains $\frac12x(1-x)$.

Partition the types into nonempty classes $C_1,\ldots,C_\ell$, and define $y_A=\sum_{a\in C_A}z_a$ and $\nu'_A=\sum_{a\in C_A}\nu_a$. If $R$ is this linear aggregation map, then

$$\sum_{a\in C_A}\frac\theta2(\nu_a-z_a)=\frac\theta2(\nu'_A-y_A),\qquad \sum_{a\in C_A,b\in C_B}z_a(\delta_{ab}-z_b)=y_A(\delta_{AB}-y_B).$$

The chain rule therefore gives $L_d(g\circ R)=(L_\ell g)\circ R$. Applying the source martingale identity to $g\circ R$ shows that aggregation maps each parent-independent solution to a solution with target law $\nu'$ and the same $\theta$. This includes merging all types to the constant one-type process. Aggregation is a pushforward, not a bijection of solution laws.

General mutation does not permit arbitrary merging. For $E=\{a,b,c\}$, let $q_{ac}=1$, $q_{bc}=2$, all other off-diagonal rates zero, and choose the diagonals to make row sums zero. After merging $\{a,b\}$, the drift into $c$ is $z_a+2z_b$. The states $(1,0,0)$ and $(0,1,0)$ have the same aggregated state but different drift, one and two. Thus no common aggregate generator valid for all initial states follows from the aggregate masses alone. Strong lumpability requires the rates $\sum_{b\in C_B}q_{ab}$ to be independent of the representative $a$ within each source class. No merging theorem for general mutation is asserted without that condition.

## Depends on

- [Generator of the K-allele Wright–Fisher diffusion with mutation and genic selection](../wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md)

## Scope

The general-$Q$ generator computation follows from the $K$-allele generator on the simplex and the cited source. Parent-independent type merging is the chain-rule derivation above. Aggregation for general $Q$ and uniqueness for the martingale problem are separate statements. A proof page must still supply the polynomial identities, the $C^2$ approximation step and the push-forward of solution laws. This algebraic result is a prerequisite for identifying the lookdown limit, not a consequence of it, and it restates no second multi-allele generator theorem.

## Sources

- M. Birkner, *Stochastic population models*, lecture notes, Johannes Gutenberg-Universität Mainz, 2025/26, <https://www.staff.uni-mainz.de/birkner/SPM2526/StochPopModels_25-26.pdf>, Sec. 1.5, (1.42)–(1.43), Remark 1.5.10, (1.47), and the monomial and derivative-approximation calculation following it. The type-merging and non-lumpability checks above are local algebraic derivations.
