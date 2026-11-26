# Determinant criterion for unique and multiple equilibria in reaction networks

**Setting.** A reaction network with $n$ species and $\ell$ reactions has stoichiometric matrix
$N \in \mathbb{R}^{n \times \ell}$ and reaction rate functions $v_j : \mathbb{R}^n_{\ge 0} \to \mathbb{R}_{\ge 0}$
of class $C^1$ that vanish exactly when some reactant species of reaction $j$ is absent (mass-action,
Michaelis–Menten and Hill kinetics qualify). The dynamics is

$$\dot x = f(x) = N v(x), \qquad x \in \mathbb{R}^n_{\ge 0}.$$

Let $s = \operatorname{rank} N$, $d = n - s$, and $W \in \mathbb{R}^{d \times n}$ a row-reduced full-rank
matrix with $W N = 0$. Trajectories stay in the stoichiometric compatibility class
$P_c = \{ x \ge 0 : W x = c \}$; write $P_c^+ = P_c \cap \mathbb{R}^n_{>0}$. Let $i_1, \dots, i_d$ be the
indices of the leading nonzero entries of the rows of $W$, and define $\varphi_c : \mathbb{R}^n_{\ge 0}
\to \mathbb{R}^n$ by replacing the redundant equations $f_{i_k}$ with the conservation laws:

$$\varphi_c(x)_i = \begin{cases} f_i(x), & i \notin \{i_1, \dots, i_d\}, \\ (W x - c)_i, & i \in \{i_1, \dots, i_d\}. \end{cases}$$

Then $P_c \cap \{ f = 0 \} = \{ x \ge 0 : \varphi_c(x) = 0 \}$. Let $M(x)$ be the Jacobian of
$\varphi_c$; it does not depend on $c$. An equilibrium $x^*$ is non-degenerate if
$\det M(x^*) \neq 0$. The network is **dissipative** if every class $P_c$ has a compact set that all
trajectories in it eventually enter.

**Theorem.** Let $P_c^+ \neq \emptyset$, and assume (i) the network is dissipative and (ii) there are
no boundary equilibria in $P_c$. Then:

1. **Uniqueness.** If $\operatorname{sign}\det M(x) = (-1)^s$ at every positive equilibrium
   $x \in P_c^+$, there is exactly one positive equilibrium in $P_c$, and it is non-degenerate.
2. **Multistationarity.** If $\operatorname{sign}\det M(x) = (-1)^{s+1}$ at some positive equilibrium
   in $P_c^+$, there are at least two positive equilibria in $P_c$, at least one non-degenerate; if
   all positive equilibria in $P_c$ are non-degenerate, their number is odd and at least three.

**Corollary.** Under (i) and (ii), if $\operatorname{sign}\det M(x) = (-1)^s$ for all
$x \in \mathbb{R}^n_{>0}$ (for instance, for injective networks), every class with nonempty interior
contains exactly one positive equilibrium, and it is non-degenerate.

## Expansion

The proof computes the Brouwer degree of $\varphi_c$ at $0$ on a bounded neighbourhood of the
compact absorbing set inside $P_c$. Dissipativity lets one homotope the vector field, within the
class, to one that points inward on the boundary of that set, and the absence of boundary equilibria
keeps zeros off the boundary during the homotopy; this forces the degree to be $(-1)^s$. Since the
degree is the sum of $\operatorname{sign}\det M(x^*)$ over the non-degenerate zeros, a single zero
of the "wrong" sign $(-1)^{s+1}$ must be compensated by at least two zeros of the right sign, giving
an odd number at least three; if every zero has the right sign, there can be only one. The only case
not covered is when $\det M$ vanishes at some equilibria but never takes the wrong sign.

## Sources

- C. Conradi, E. Feliu, M. Mincheva, C. Wiuf, "Identifying parameter regions for
  multistationarity", PLoS Computational Biology 13 (2017) e1005751, Eqs. (2)-(6), Theorem 1 and
  Corollary 1, <https://doi.org/10.1371/journal.pcbi.1005751> (PMC5626113).
