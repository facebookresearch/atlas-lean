# Circuit growth-index criterion for dispersal-induced growth on periodically switching networks

**Model.** A population lives on $n$ sites. A period $T$ is split into $p$ seasons $[Tt_{k-1}, Tt_k)$, $0 = t_0 < \dots < t_p = 1$. In season $k$ site $i$ has growth rate $r_i^k$ and individuals move from site $j$ to site $i$ along the oriented links of a network $\mathcal{N}^k$ with rates $m\ell_{ij}^k$ ($m \ge 0$ the migration strength):

$$\frac{dx_i}{dt} = r_i^k x_i + m\sum_{j=1}^n \ell_{ij}^k x_j, \qquad t \in [Tt_{k-1}, Tt_k),$$

with $\ell_{ij}^k \ge 0$ for $i \ne j$ and $\sum_i \ell_{ij}^k = 0$ (migration conserves individuals). The system is a *source* if the total population $S(t) = \sum_i x_i(t)$ tends to infinity, and $m^*(T) = \inf\{m : S(t,m,T) \to \infty\}$. Assume every site is a sink in isolation, $\sum_k r_i^k(t_k - t_{k-1}) < 0$. *Dispersal-induced growth* (DIG) occurs if the system is a source for some $(m,T)$.

**Growth indices.** The growth index is $\chi = \sum_{k=1}^p (t_k - t_{k-1})\max_i r_i^k$. A $p$-circuit $\mathcal{C} = a_0\Gamma^1a_1\Gamma^2a_2\cdots\Gamma^pa_0$ concatenates, for each season $k$, a directed path $\Gamma^k$ in $\mathcal{N}^k$ from site $a_{k-1}$ to site $a_k$, returning to $a_0$; its growth index is

$$\chi^{\mathcal{C}} = \sum_{k=1}^p (t_k - t_{k-1})\max_{\pi_i \in \Gamma^k} r_i^k \le \chi.$$

**Theorem.**
1. (Necessary condition.) If the system is a source for some $(m,T)$, then $\chi > 0$, since $dS/dt \le (\max_i r_i(t))S$.
2. (Sufficient condition.) If some $p$-circuit $\mathcal{C}$ has $\chi^{\mathcal{C}} > 0$, then for every large enough $\tau$ there are $0 < a(\tau) < b(\tau)$ such that the system is a source whenever $T \ge \tau$ and $m \in [a(\tau), b(\tau)]$: DIG holds.
3. (Quantitative bound.) For such a circuit, with total length $L$, there are $\tau, C, \mu > 0$ independent of $m$ with

$$x_{a_0}(T) \ge C\,m^{L}\,e^{T(\chi^{\mathcal{C}} - \mu m)}\,x_{a_0}(0) \qquad (T > \tau),$$

and consequently $m^*(T) \le e^{-\alpha T}$ for some $\alpha > 0$ and all large $T$: the migration threshold for growth is exponentially small in the period.
4. The same holds for circuits that wind $q$ times through the $p$ seasons, and for random season lengths, where $m^*(T) \le e^{-(1-\varepsilon)T\chi^{\mathcal{C}}_{\mathrm{stoc}}/L}$ almost surely for large $T$.

When every $\mathcal{N}^k$ is strongly connected some circuit attains $\chi^{\mathcal{C}} = \chi$, recovering the criterion "$\chi > 0$ iff DIG"; for non-strongly-connected networks $\chi > 0$ alone does not suffice.

## Expansion

With weak migration and long seasons, a small fraction of the population can follow the circuit: during season $k$ it travels along $\Gamma^k$ to the best site on that path, grows there at rate $\max_{\Gamma^k} r_i^k$ for most of the season, and moves on in time for the next season. Each move costs a factor of order $m$ (one factor per link, hence $m^L$) and the time spent in transit costs $O(mT)$ in the exponent, so the circuit population grows like $m^L e^{T(\chi^{\mathcal{C}} - \mu m)}$, which exceeds $1$ for $m$ in a window $[a(\tau), b(\tau)]$ once $T$ is large. The proof uses only positivity of Metzler-matrix exponentials and the variation-of-constants formula, avoiding Floquet or Lyapunov-exponent machinery.

## Sources

- M. Benaïm, C. Lobry, T. Sari, E. Strickler, "Sufficient condition for dispersal-induced growth on dynamic networks", arXiv:2411.07821 (2024), model and Definitions of Section 2 (source, $m^*(T)$, DIG, growth indices), Propositions 1–8, <https://doi.org/10.48550/arXiv.2411.07821>.
