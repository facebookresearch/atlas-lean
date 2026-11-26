# Ambient Gram and ellipsoid estimates for finite-memory Gaussian regression

For a finite measure $\mu$ on $\mathbb R^d$, centered support condition $\operatorname{supp}\mu\subseteq\overline B(z,R)$, and $H,R>0$, say it has $(H,\beta)$ growth if $\mu(\overline B(x,t))\le Ht^\beta$ for every center $x$ and $t>0$. Assume $d,m\ge1$, $p\ge2$ natural and $\beta>m+p-2$. Set

$$
J_j=1+3^j2^\beta\frac{m}{\beta-j-m},\qquad
B=(2\pi)^{-m(p-1)/(2p)}H R^{\beta-m(1-1/p)}\left(\prod_{j=0}^{p-2}J_j\right)^{1/p}.
$$

For each nonempty affine $j$-plane $L$, $j\le p-2$, the mass within distance $t\in(0,R]$ is at most $3^j2^\beta HR^jt^{\beta-j}$. The integral of $\operatorname{dist}(x,L)^{-m}$ with extended reciprocals is at most $J_j HR^{\beta-m}$. For $p$ independent points under the product measure of $\mu$, their differences from the first are almost everywhere linearly independent. The integral of their inverse Gram volume to the $m$th power is at most $H^pR^{\beta p-m(p-1)}\prod_{j=0}^{p-2}J_j$ (for this Gram integrand the source applies the real reciprocal then embeds it). For $d\ge16$, $p=\lfloor d/8\rfloor$, $1\le m\le p$ and $(d-1)/2\le\beta\le d/2$, for $j\le p-2$ one has

$$
d/4+3/2\le(d-1)/2-2p+2\le\beta-j-m,\qquad J_j\le C^d
$$

for a universal $C\ge1$. The same source statement bounds the moment above by $C^{d(p-1)}H^pR^{\beta p-m(p-1)}$.

For $A$ an independent standard Gaussian array of $m$ rows, let $\eta$ be the law (finite measure) of $(A,As)$ with $s$ sampled from $\mu$ and let $\nu$ be the product Gaussian-row law times Lebesgue label volume. Put $E=\{(A,y): y=Az+Av,\ \|v\|\le R\}$. Under the general growth and support assumptions above:

* There exists a measurable nonnegative real density $F$ of $\eta$ relative to $\nu$ supported almost everywhere on $E$, with $\|F\|_{L^p(\nu)}\le B$.
* Every measurable event of finite $\nu$-mass satisfies $\eta(U)\le B\nu(U)^{1-1/p}$, and $\eta\ll\nu$. There is an extension to the measurable space of $\nu$-null-measurable sets, agreeing with $\eta$ on each such set. On any such set $U$ of finite completed-reference mass it satisfies $\eta_c(U)\le B[\nu^{\rm completion}(U)]^{1-1/p}$. For every measurable $0\le f\le1$ on the completed space, its extended integral against this extension is at most $B(\int_E f\,d\nu)^{1-1/p}$, using completed $\nu$.
* If also $d\ge2$, $m<d$, and $\mu$ is absolutely continuous with respect to normalized sphere measure, then Gaussian smoothing of the labels by $N(0,\delta^2 I_m)$ tends to any nonnegative measurable density $F$ of $\eta$ in joint $L^1(\nu)$ as $\delta\downarrow0$, and every such $F$ has $L^p$ norm at most $B$.
* Under those same spherical hypotheses a pointwise version defined by the real filter limit, if one exists, of the smoothed densities at $\delta=1/j$ for natural $j\to\infty$ (totalized inverse at $j=0$, and the density version is zero when there is no real limit) is measurable and nonnegative, gives the label pushforward density for every full-rank $A$, gives the joint density, agrees almost everywhere with any other nonnegative measurable version, and has integrated $p$th power at most $B^p$. For each $\delta>0$ the Gaussian smoothing kernel $g_\delta$ is a radial mixture of uniform ball kernels: with $v_m$ the unit ball volume the mixing density on $r>0$ is $v_mr^m(r/\delta^2)g_\delta(re_1)$, nonnegative, measurable, of integral one, and integrating that density divided by $v_mr^m$ over $r>\|y\|$ gives $g_\delta(y)$.

For the block statements, when $d\ge16$, $N\ge1$, take a measurable array of weights $0\le h_w\le1$ on signals for $w<N$ and measurable tests $g_w(A,y)\ge0$ with sum at most one. The new weight at signal $s$ is $\mathbb E_A\sum_w h_w(s)g_w(A,As)$. For sphere signals, if each weighted sphere measure $h_w\sigma_d$ has $(H,\alpha)$ growth at every ambient center and positive radius with $H>0$, $(d-1)/2\le\alpha\le d/2$, then for $1\le m\le\lfloor d/8\rfloor$ the new sphere weight has $(C^d N^{1/\lfloor d/8\rfloor}H,\alpha)$ growth for one universal $C\ge1$. For cube signals let $s=s(u)=n^{-1/2}(u_1,\ldots,u_n,\sqrt{1-u_1^2},\ldots,\sqrt{1-u_n^2},0,\ldots,0)$ with $n=\lfloor d/2\rfloor$ and uniform $u\in[-1/2,1/2]^n$. Use local mass tested in cube-space balls of radius $\sqrt n\,r$, with bound $Lr^{3n/4}$ for all centers and positive $r$. For $L\ge0$ and $1\le k\le\lfloor n/4\rfloor$ rows the new coefficient is $C^n N^{1/\lfloor n/4\rfloor}L$, with the same growth exponent.

For streaming, take an arbitrary probability law for the seed. Use $2^M$ states and a seed independent of the rows and of the chosen prior sample, with a possibly different randomized policy at each seed. A policy gives distributions on (stop bit, state) at initialization and at each time from the current state and exact Gaussian row/label pair, with unit-output law depending on time and state. Recursively average any output test over this policy through $T$ with early stopping. For almost every seed, every transition atom map (at each time, current state and destination action) is almost-everywhere measurable with respect to Gaussian row times Lebesgue label. For a particular prior, admissibility also requires that for every measurable extended nonnegative test $f(s,v)\le1$ of signal and output, the iterated test value is almost-everywhere measurable under the prior times the product of seed law and Gaussian rows. The terminal test is the lower integral of $f(s,v)$ under the output law at that time and state; take the lower integral of the iterated test to define success for the angle or chord indicator. All-prior admissibility quantifies this same condition over **every** probability law on the unit sphere, with the same policy assignment and seed law. Write $S_{\rm ang}$ and $S_{\rm chord}$ for success at angular or Euclidean chord radius $\varepsilon$, and $b(T,k)=\lceil T/k\rceil$. For $0<\varepsilon\le1/10$ the selected bounds are:

* There are absolute $C,C_0\ge1$ such that for every $d\ge16$ with $p=\lfloor d/8\rfloor$, every $M,T$, every probability seed law and every seeded policy admissible for the uniform sphere prior, the pair $C,C_0$ bounds $S_{\rm ang}$ by $\min\{1,4^d\varepsilon^{(d-1)/2}[C^d((p+2)2^M)^{1/p}]^{b(T,p)}\}$ and $S_{\rm chord}$ by $\min\{1,C_0^d\varepsilon^{d/2-1}[C^d((2p+4)2^M)^{1/p}]^{b(T,p)}\}$. The angular-success event is contained in the chord-success event at the same tolerance.
* There are $D\ge e$, $d_0\ge16$, $c>0$ such that for $d\ge d_0$, $M\le d^2$, and policies admissible at every probability prior, the cube-prior $S_{\rm ang}$ is at most $\min\{1,D^{n(b(T,k)+1)}\varepsilon^{n/4}\}$ with $n=\lfloor d/2\rfloor$, $k=\lfloor n/4\rfloor$. If fixed-signal success is at least $2/3$ for every unit signal, $T\ge cd\log(1/\varepsilon)$.
* There are $C>0,d_0>0$ such that for all $d\ge d_0$, every $M,T$, every probability seed law and every seeded policy admissible for the uniform sphere prior, $S_{\rm ang}\le\min\{1,[2\varepsilon\exp(C(1+M/d^2)b(T,\lfloor(d-1)/8\rfloor))]^{(d-1)/2}\}$.

**Conventions.** Use ambient Euclidean growth, inverse Gram volumes and exact random-projection densities, measure completion, the normalized cube chart, and seeded finite-state policies with early stopping and the stated measurability conditions.

## Depends on

- [Completed-rule Gaussian policies and prior-dependent admissibility](models/completed-early-stopping-policy.md)

- [Noiseless Gaussian row and label density models](gaussian-projection-density-model.md)

## Proof depends on

A covering and inverse-distance estimate for affine planes, the Gram factorization, Gaussian smoothing and differentiation including the joint label density, and separate sphere and cube block recurrences feeding the finite-memory precision bounds.

## Expansion

Separate the geometric estimates, density existence and versions, completion bound, sphere and cube recurrences, and success bounds into independent statements. Verify the radial mixture and normalization in the label dimension, preserve the distinct angular and chord exponents and state factors, and keep pointwise-signal success separate from prior-averaged success.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MemoryPrecision.lean#L771-L807)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/140.md)
- [Accompanying manuscript: Memory and precision in noiseless Gaussian regression](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Memory-and-precision-in-noiseless-Gaussian-regression-September-27-2026/paper.pdf)
