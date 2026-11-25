# Beta-mixture marginals for every mutation Wright-Fisher solution

Let $\theta_1,\theta_2>0$, $\theta=\theta_1+\theta_2$, and let $X$ solve
the [selection-mutation martingale problem](../wright-fisher-diffusion-with-mutation/two-way-mutation-and-selection-wright-fisher-mar.md)
with $\alpha=0$ and $X_0=x\in[0,1]$ almost surely.
Let $q_n^\theta(t)$ be the [entrance probabilities of the pure-death line count](transition-probabilities-q-theta-n-t-of-the-non.md)
with rates $\lambda_n=n(n+\theta-1)/2$. For every $t>0$,

$$\mathcal L(X_t)=K_t(x,\cdot):=
 \sum_{n=0}^\infty q_n^\theta(t)
 \sum_{l=0}^n\binom nl x^l(1-x)^{n-l}
 \operatorname{Beta}(\theta_1+l,\theta_2+n-l).$$

Use the usual binomial endpoint conventions, including $0^0=1$.
The positive parameters make every Beta law a probability measure on
$[0,1]$; the displayed mixture is a probability measure. At time zero set
$K_0(x,\cdot)=\delta_x$ rather than using a finite-state entrance distribution.
The formula identifies the marginal of any solution; it does not assume or
prove existence of the canonical continuous-path process.

The kernels $K_t$ preserve $\operatorname{Beta}(\theta_1,\theta_2)$ and
converge to it in total variation uniformly in $x$. More precisely, for
$d_{\rm TV}(\mu,\nu)=\sup_A|\mu(A)-\nu(A)|$,

$$d_{\rm TV}(K_t(x,\cdot),\operatorname{Beta}(\theta_1,\theta_2))
 \le1-q_0^\theta(t)\longrightarrow0.$$

## Depends on

- [Martingale problem with selection and mutation](../wright-fisher-diffusion-with-mutation/two-way-mutation-and-selection-wright-fisher-mar.md)
- [Pure-death entrance probabilities](transition-probabilities-q-theta-n-t-of-the-non.md)

## Proof depends on

- [Pure-death entrance process and absorption](transition-probabilities-q-theta-n-t-of-the-non.md)
- [Killed moment duality and its finite moment equations](../wright-fisher-diffusion-with-mutation/moment-duality-with-mutation-killed-absorbed-blo.md)
- [Compactly supported measures are determined by their moments](../../../../Analysis/harmonic-analysis/integral-transforms/moment-problem-for-compactly-supported-measures/ext-of-forall-integral-pow-eq-of-compl-i.md)

## Expansion

Let $K^{(n)}(x,\cdot)$ be the inner binomial-Beta mixture, and put

$$g_{n,k}(x)=\int y^kK^{(n)}(x,dy)
 =\sum_{l=0}^n\binom nl x^l(1-x)^{n-l}
   \frac{(\theta_1+l)_{(k)}}{(\theta+n)_{(k)}}.$$

The Beta moment formula follows by taking the ratio of the Beta integrals
$B(a+k,b)/B(a,b)$. With $a_k=k(k-1+\theta_1)/2$, direct finite binomial and
rising-factorial algebra gives, for $n\ge1,k\ge1$,

$$\lambda_n(g_{n-1,k}-g_{n,k})
 =a_kg_{n,k-1}-\lambda_kg_{n,k}.$$

The degree-$n$ Bernstein coefficient of the left side, at index $l$, is
$\tfrac{k}{2}[n(\theta_1+l)_{(k)}/(\theta+n)_{(k)}
-l(\theta_1+l)_{(k-1)}/(\theta+n)_{(k-1)}]$;
the rising-factorial recurrence identifies it with the right-side
coefficient. For $n=0$ the right side is zero, by the Beta moment recurrence.
This is the bridge between the pure-death mixture count and the different killed dual;
the two chains are not identified.

For fixed $k$, $g_{n,k}(x)\to x^k$ uniformly in $x\in[0,1]$. One proof
samples $L\sim\operatorname{Bin}(n,x)$ and
$Y\mid L\sim\operatorname{Beta}(\theta_1+L,\theta_2+n-L)$: its bias is
$(\theta_1-\theta x)/(\theta+n)$, and

$$\operatorname{Var}(Y)\le\frac1{4(\theta+n+1)}+
 \frac{n}{4(\theta+n)^2}.$$

Cauchy-Schwarz and $|Y^k-x^k|\le k|Y-x|$ finish the argument.
For the entrance chain $B$, apply its backward/Dynkin identity to the
bounded function $n\mapsto g_{n,k}(x)$ starting at time $\varepsilon>0$.
Its generator is uniformly bounded by the displayed finite identity.
Let $\varepsilon\downarrow0$; bounded convergence and $B_\varepsilon\to\infty$
give for $u_k(t)=\sum_nq_n^\theta(t)g_{n,k}(x)$ the integral equations

$$u'_k=a_ku_{k-1}-\lambda_ku_k,\qquad u_0=1,\quad u_k(0)=x^k.$$

These are the solution's moment equations. Finite triangular-system
uniqueness and moment determinacy on $[0,1]$ identify the laws. This route
does not differentiate or rearrange unbounded alternating series at zero.

Every $K^{(n)}$ preserves the Beta prior: multiplying its binomial sampling
probabilities by that prior and integrating gives the beta-binomial
predictive probabilities, whose Beta posteriors mix back to the prior.
Equivalently this follows by canceling Beta normalizers and summing the
binomial theorem. Therefore $K_t$ also preserves it. The $n=0$ component
is the prior itself, and the entrance chain reaches zero in finite time
almost surely; this proves the total-variation bound and limit.

## Sources

- O. Papaspiliopoulos, M. Ruggiero and D. Spanò, "Conjugacy properties of time-evolving Dirichlet and gamma random measures", Electronic Journal of Statistics 10 (2016), 3452–3489, <https://doi.org/10.1214/16-EJS1194>, preprint <https://arxiv.org/abs/1607.02896>, Section 2.1.2, equation (11) and the death-process definition before it. The displayed mixture is the two-type projection; the source attributes the transition representation to Ethier and Griffiths (1993).
- S. Tavaré, "Line-of-descent and genealogical processes, and their applications in population genetics models", Theoretical Population Biology 26 (1984), 119–164, <https://doi.org/10.1016/0040-5809(84)90027-3>, Section 5.2 and Section 7.5, (7.21)–(7.23), for the corresponding one-way case. The argument for every solution and the precise convergence bound are supplied above.
