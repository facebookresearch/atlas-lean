# Glivenko–Cantelli theorem for the fitness-threshold ecosystem

**Model.** The Guiol–Machado–Schinazi model of species survival, as generalized by Michael and Volkov, describes an ecosystem in which every member gets an independent $U[0,1]$ "fitness" at birth and the least fit members are removed when the population shrinks. Let $I,I_1,I_2,\dots$ be i.i.d. $\mathbb{Z}$-valued increments. The population size is the reflected walk

$$X_0=0,\qquad X_{n+1}=X_n+\max(I_{n+1},-X_n):$$

at step $n+1$, $I_{n+1}$ newborns arrive if $I_{n+1}\ge0$, and otherwise the $\min(X_n,|I_{n+1}|)$ members of lowest fitness die. Let $L_n(f)$ be the number of members at time $n$ with fitness at most $f\in[0,1]$, so $L_n(1)=X_n$.

**Reflected random walk representation.** With $x_\pm$ the positive and negative parts, let $C_j(f)$ be the number of members born at step $j$ with fitness at most $f$, and

$$S_n(f)=\sum_{0<j\le n}\big(C_j(f)-(I_j)_-\big),\qquad M_n(f)=\min_{0\le k\le n}S_k(f) .$$

Then for every $f$ and $n$,

$$L_n(f)=S_n(f)-M_n(f),$$

so $(L(f))_{f\in[0,1]}$ is a family of coupled reflected random walks, each a Markov chain on $\mathbb{Z}_+$.

**Critical fitness.** Assume $\mathbb{E}I_-<\mathbb{E}I_+\le\infty$, so $X_n\to\infty$ almost surely, and set

$$f_c=\frac{\mathbb{E}I_-}{\mathbb{E}I_+}\in[0,1) .$$

For $f<f_c$ the walk $S(f)$ has negative drift $f\,\mathbb{E}I_+-\mathbb{E}I_-$ and $L(f)$ is positive recurrent; for $f>f_c$ it is transient.

**Theorem.** Let $\hat F_n(f)=L_n(f)/X_n$ (and $0$ if $X_n=0$) be the empirical fitness distribution, and let $F(f)=(\min(f,1)-f_c)_+/(1-f_c)$ be the distribution function of $U[f_c,1]$. Under $\mathbb{E}I_-<\mathbb{E}I_+$,

$$\lim_{n\to\infty}\ \sup_{f\in[0,1]}\big|\hat F_n(f)-F(f)\big|=0\quad\text{almost surely.}$$

So the surviving fitnesses are asymptotically uniform on $[f_c,1]$: the population self-organizes above a sharp threshold, unlike the classical Glivenko–Cantelli limit, which is the sampling law itself.

## Expansion

The representation is the Lindley recursion for reflected walks, proved by induction from $L_{n+1}(f)=L_n(f)+\max(C_{n+1}(f)-(I_{n+1})_-,-L_n(f))$. For the limit, the strong law gives $S_n(f)/n\to f\,\mathbb{E}I_+-\mathbb{E}I_-$, and $M_n(f)/n\to -(f-f_c)_-\mathbb{E}I_+$ since the running minimum grows linearly exactly when the drift is negative. Hence $L_n(f)/n\to(f-f_c)_+\mathbb{E}I_+$ almost surely, and dividing by $X_n/n\to(1-f_c)\mathbb{E}I_+$ gives pointwise convergence to $F$. Monotonicity of $f\mapsto L_n(f)$ and continuity of $F$ upgrade this to uniform convergence, as in the classical Glivenko–Cantelli argument. The result is equivalent to Michael and Volkov's coupling theorem.

## Sources

- Iddo Ben-Ari, "An Empirical Process Interpretation of a Model of Species Survival", arXiv:1210.1112 (2012): Lemma 1 (reflected walk representation), Theorem 1 (Glivenko–Cantelli analog), Lemma 3 (linear growth of $L_n$ and $M_n$), Sections 1–2. <https://doi.org/10.48550/arXiv.1210.1112>. Published version: Stochastic Processes and their Applications 123(2) (2013), 475–489, <https://doi.org/10.1016/j.spa.2012.09.009>; locators above refer to the arXiv version.
