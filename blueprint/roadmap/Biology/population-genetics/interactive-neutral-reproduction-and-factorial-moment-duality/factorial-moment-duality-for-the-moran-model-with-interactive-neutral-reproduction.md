# Factorial moment duality for the Moran model with interactive neutral reproduction

**Model.** A haploid population of $N$ individuals of type $0$ (fit) or $1$ (unfit) evolves in continuous time; each individual independently undergoes:

- neutral reproduction at rate $r/2$: it is replaced by the offspring of a uniformly chosen individual;
- interactive neutral reproduction at rate $\kappa/2$: it samples two individuals with replacement; if the first (checking) one is fit, the second reproduces and its offspring replaces the initiator;
- fittest-type-wins selection of order $m\ge1$ at rate $s_m$: it samples $m$ individuals with replacement and, if at least one is fit, is replaced by a fit offspring;
- mutation to type $j\in\{0,1\}$ at rate $u\nu_j$, $\nu_0+\nu_1=1$.

The number $X^{(N)}_t$ of unfit individuals is a birth–death chain on $\{0,\dots,N\}$ jumping $n\to n+1$ at rate $\frac r2(N-n)\frac nN+\frac\kappa2(N-n)\frac nN\frac{N-n}N+(N-n)u\nu_1$ and $n\to n-1$ at rate $\frac r2n\frac{N-n}N+\frac\kappa2n(\frac{N-n}N)^2+nu\nu_0+\sum_m s_mn(1-(\frac nN)^m)$.

**Dual chain.** Let $p^n_{mj}$ be the probability that $m$ draws with replacement from $[N]$ hit exactly $j$ distinct elements outside $[n]$. $Z^{(N)}$ is the chain on $\{0,\dots,N\}\cup\{\Delta\}$ with
$$n\to n+j\ (j\ge2)\ \text{at rate}\ n\sum_{m\ge j}s_mp^n_{mj},\qquad n\to n+1\ \text{at rate}\ \tfrac\kappa N\tbinom n2\tfrac{N-n}N+n\sum_m s_mp^n_{m1},$$
$$n\to n-1\ \text{at rate}\ \tfrac1N\tbinom n2\big(r+\kappa\tfrac{N-(n-1)}N\big)+u\nu_1n,\qquad n\to\Delta\ \text{at rate}\ u\nu_0n .$$

**Theorem (factorial moment duality).** For all $t\ge0$, $n\in\{0,\dots,N\}\cup\{\Delta\}$ and $i\in\{0,\dots,N\}$, with falling factorials $x^{\underline n}$ and the convention $i^{\underline\Delta}=0$,
$$\mathbb E\Big[\frac{(X^{(N)}_t)^{\underline n}}{N^{\underline n}}\ \Big|\ X^{(N)}_0=i\Big]=\mathbb E\Big[\frac{i^{\underline{Z^{(N)}_t}}}{N^{\underline{Z^{(N)}_t}}}\ \Big|\ Z^{(N)}_0=n\Big].$$
The left side is the probability that $n$ individuals sampled without replacement at time $t$ are all unfit.

**Diffusion limit and moment duality.** If $Nu\to\theta$, $Ns_m\to\sigma_m$ with $\sum_m m\sigma_m<\infty$, then $X^{(N)}_{Nt}/N$ converges to the solution of
$$dX_t=\Big(-\sum_{m\ge1}\sigma_mX_t(1-X_t^m)+\theta\nu_1(1-X_t)-\theta\nu_0X_t\Big)dt+\sqrt{X_t(1-X_t)\big(r+\kappa(1-X_t)\big)}\,dB_t,$$
$Z^{(N)}_{Nt}$ converges to the chain $Z$ with $n\to n+m$ at rate $\sigma_mn$ ($m\ge2$), $n\to n+1$ at rate $\kappa\binom n2+\sigma_1n$, $n\to n-1$ at rate $(r+\kappa)\binom n2+\theta\nu_1n$, $n\to\Delta$ at rate $\theta\nu_0n$, and
$$\mathbb E[X_t^n\mid X_0=x]=\mathbb E[x^{Z_t}\mid Z_0=n].$$
With $r=1-\kappa$ and no selection or mutation this is the dual of $dX=\sqrt{X(1-X)(1-\kappa X)}\,dB$, a birth–death process with pairwise branching and pairwise coalescence.

## Depends on

- [Moran model](../moran-model/README.md)
- [Wright–Fisher semigroup and moment duality](../diffusion-theory/wright-fisher-semigroup-and-moment-duality/README.md)

## Expansion

For selection and mutation the dual comes from pruning the ancestral selection graph as usual. Interactive events are harder: an unfit sample can have fit potential influencers, so no pathwise duality exists. The proof works on the ancestral influence graph with the roles of checking and parental lines forgotten (a quasi-AIG), tracks ordered typed samples (configurations), and shows by a matching argument (the Frankenstein matching) that averaging over the two role assignments of each interactive event produces a set of configurations whose count of all-unfit lines is a Markov chain with the law of $Z^{(N)}$. In the limit the generator of $X$ applied to $x^n$ equals the generator of $Z$ applied to $n\mapsto x^n$; for example the diffusion term gives $\binom n2(r+\kappa)(x^{n-1}-x^n)+\kappa\binom n2(x^{n+1}-x^n)$.

## Sources

- E. Baake, F. Cordero, H. Dopmeyer, "Genealogical structures under interactive neutral reproduction: factorial moment duality via a Frankenstein process", arXiv:2605.02499 (2026), Section 2 (model, Definition of $Z^{(N)}$, Theorem 1, Corollary 1), Section 4 (Proposition 1, Proposition 2), Section 5 (Propositions 5–7), <https://doi.org/10.48550/arXiv.2605.02499>.
