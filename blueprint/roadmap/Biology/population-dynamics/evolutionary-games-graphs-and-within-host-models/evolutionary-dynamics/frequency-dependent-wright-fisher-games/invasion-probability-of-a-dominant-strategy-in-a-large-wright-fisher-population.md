# Invasion probability of a dominant strategy in a large Wright–Fisher population

Two strategies $A$ and $B$ play a symmetric $2\times2$ game with positive payoffs $a$ ($A$ vs $A$), $b$ ($A$ vs $B$), $c$ ($B$ vs $A$), $d$ ($B$ vs $B$). In a population of size $N$ with $i$ individuals of type $A$, fitnesses are $f_N(i)=1-w+w\frac{a(i-1)+b(N-i)}{N-1}$ and $g_N(i)=1-w+w\frac{ci+d(N-i-1)}{N-1}$ with selection parameter $w\in(0,1)$. The Wright–Fisher chain moves from $i$ to $\mathrm{Bin}(N,\xi_N(i))$, where

$$ \xi_N(i)=\frac{i f_N(i)}{i f_N(i)+(N-i)g_N(i)}, $$

and $p_N(i)$ is the probability of absorption at $N$ (fixation of $A$) from $i$. Assume (strong selection for $A$) that there are $N_0\ge2$ and constants $0<\alpha\le\gamma<1$ with $\alpha\le g_N(i)/f_N(i)\le\gamma$ for all $N\ge N_0$ and $1\le i\le N-1$; since $f_N,g_N$ are linear in $i$, this holds when $A$ strictly dominates, $a>c$ and $b>d$.

**Theorem.** For every fixed $i\ge1$ the limit $\lim_{N\to\infty}p_N(i)$ exists and

$$ \lim_{N\to\infty}p_N(i)=1-q^i,\qquad q=e^{-\lambda(1-q)},\qquad \lambda=\frac{1-w+wb}{1-w+wd}, $$

where $q$ is the unique root in $(0,1)$ (it exists because $\lambda>1$ when $b>d$). Thus $i$ mutants playing the dominant strategy invade an infinitely large resident population with positive probability, equal to the survival probability of $i$ independent Galton–Watson processes with Poisson($\lambda$) offspring. With the explicit constants $\theta=e^{-2(1-\alpha)/\alpha}\le\rho=e^{-2(1-\gamma)}$ of the finite-$N$ bounds one has $\theta\le q\le\rho$. The same paper gives two-sided bounds on the law of the fixation time, $P(T\le m\mid X_0=k)$, in terms of $\lambda$ and $q$ up to errors of order $J^{3/2}/N$.

## Proof depends on

- [Moran-type bounds for fixation in the frequency-dependent Wright–Fisher process](moran-type-bounds-for-fixation-in-the-frequency-dependent-wright-fisher-process.md)

## Expansion

While the number of mutants $i$ stays small compared with $N$, $\xi_N(i)\approx i\lambda/N$ because $f_N(i)\to1-w+wb$ and $g_N(i)\to1-w+wd$; hence $X_{t+1}$ is approximately Poisson with mean $\lambda X_t$, a supercritical branching process. Extinction of the mutants corresponds to extinction of that branching process, whose probability from one ancestor is the root $q<1$ of the Poisson generating-function equation $q=e^{-\lambda(1-q)}$. Once the mutant count grows large, the finite-$N$ bounds force fixation with probability tending to one, which identifies the limit.

## Sources

- T. Chumley, O. Aydogmus, A. Matzavinos and A. Roitershtein, "Moran-type bounds for the fixation probability in a frequency-dependent Wright–Fisher model", arXiv:1609.00838 (2016), <https://doi.org/10.48550/arXiv.1609.00838>. Theorem 10 (limit of the fixation probability), Theorem 2 (summary of the bounds and the limit), Theorem 11 (fixation-time bounds). The ordering $\theta\le q\le\rho$ follows by letting $N\to\infty$ in Theorem 5. Published version: Journal of Mathematical Biology 76 (2018) 1–35, <https://doi.org/10.1007/s00285-017-1137-2>.
