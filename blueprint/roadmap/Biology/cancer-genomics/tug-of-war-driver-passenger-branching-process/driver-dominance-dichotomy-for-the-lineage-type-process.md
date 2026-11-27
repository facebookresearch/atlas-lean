# Driver-dominance dichotomy for the lineage type process

**Model.** A cell carrying $n_d$ drivers and $n_p$ passengers divides at rate $b=b_0(1+s_d)^{n_d}/(1+s_p)^{n_p}$ and dies at rate $d=1$, with $b_0>d$ and $s_d>s_p>0$. Drivers arrive at rate $\mu$, passengers at rate $\nu$, with $\mu<\nu$. Assume $1+s_d=(1+s_p)^L$ for an integer $L\ge2$. Then the type $i=n_dL-n_p\in\mathbb{Z}$ determines the birth rate $b(i)=b_0(1+s_p)^{i}$, and a type-$i$ cell
- divides into two type-$i$ cells at rate $b(i)$,
- becomes type $i+L$ (driver) at rate $\mu$,
- becomes type $i-1$ (passenger) at rate $\nu$,
- dies at rate $d$.

The process starts from one type-$0$ cell and is non-explosive when $\nu+d>\mu L$. Let $q_i$ be the probability of global extinction from one type-$i$ cell and $\delta(i)=b(i)+\mu+\nu+d$; then

$$q_i=\frac{d}{\delta(i)}+\frac{\nu}{\delta(i)}q_{i-1}+\frac{b(i)}{\delta(i)}q_i^2+\frac{\mu}{\delta(i)}q_{i+L}.$$

**Lineage type process.** Following one infinite (surviving) line of descent, the type evolves as a Markov chain with transition probabilities obtained by conditioning on survival; its jump chain $(Y_n)$ moves $i\to i-1$ and $i\to i+L$ with probabilities proportional to $\nu(1-q_{i-1})/(1-q_i)$ and $\mu(1-q_{i+L})/(1-q_i)$, and $(X_t)$ is the corresponding continuous-time process with $X_0=Y_0=0$.

**Statements.**
1. *(Survival.)* All $q_i<1$, and $i>j$ implies $q_i\le q_j$; moreover $q_i\to0$ as $i\to\infty$ and $q_i\to1$ as $i\to-\infty$.
2. *(Driver dominance.)* If $\nu\le\mu L$, then $(Y_n)$ and $(X_t)$ are transient: the expected type and the expected fitness $\mathbb{E}\,b(X_t)$ along the lineage diverge, and there is no limiting type distribution.
3. *(Passenger dominance.)* If $\nu>\mu L$, then $(Y_n)$ is positive recurrent and $(X_t)$ has a limiting distribution: fitness along surviving lineages stabilizes.

## Expansion

Monotonicity of $q_i$ follows by coupling a fitter founder with a less fit one. The conditional drift of the jump chain is $\mathbb{E}[Y_{n+1}-i\mid Y_n=i]\propto\mu L(1-q_{i+L})-\nu(1-q_{i-1})$; since $q_i$ decreases in $i$, this is at least $\mu L-\nu$ times a positive factor at high types, so for $\nu\le\mu L$ the chain is a submartingale with the transience criterion $q_i\le d/b(i)$. For $\nu>\mu L$, at high types $q_{i\pm}\approx0$ and the drift is $\approx\mu L-\nu<0$, while at very negative types survival forces upward moves, so a Foster-Lyapunov argument (via a discrete Levinson theorem for the asymptotics of $q_i$) gives positive recurrence. The threshold $\nu=\mu L$ is exactly where the mean fitness change per mutation event, $+L$ at rate $\mu$ against $-1$ at rate $\nu$, vanishes.

## Sources

- Ren-Yi Wang and Marek Kimmel, "A Countable-Type Branching Process Model for the Tug-of-War Cancer Cell Dynamics", Bulletin of Mathematical Biology 86 (2024), 18, <https://doi.org/10.1007/s11538-023-01245-1>; numbering as in arXiv:2302.08695: Section 2 (model and driver-passenger reduction), Section 3 (extinction equations and type transition process), Appendix theorems on monotonicity of extinction probabilities, transience for $\nu\le\mu L$ and positive recurrence for $\nu>\mu L$.
