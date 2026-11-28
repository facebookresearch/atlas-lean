# R-max attains near-optimal average reward in polynomial time

In a fixed-sum stochastic game with $N$ states, $k$ actions, payoffs in $[0, R_{\max}]$, R-max with a suitable visit threshold earns, with probability $1-\delta$, average reward over its first $t_0$ steps of at least the best guaranteed return of policies with $\varepsilon$-return mixing time at most $T$, minus $2\varepsilon$; $t_0$ is polynomial in $N$, $k$, $T$, $1/\varepsilon$, $1/\delta$ for fixed $R_{\max}$.

**Theorem.** Let $M$ be a fixed-sum two-player stochastic game with $N$ states and $k$ actions whose payoffs are normalized to $[0, R_{\max}]$, where $R_{\max} > 0$ is a fixed constant known to the agent, and let $0 < \delta < 1$, $\varepsilon > 0$ and $T \ge 1$. Let $\Pi_M(\varepsilon, T)$ be the set of policies whose (adversarial) $\varepsilon$-return mixing time is at most $T$, and let

$$\mathrm{Opt}(\Pi_M(\varepsilon, T)) = \sup_{\pi \in \Pi_M(\varepsilon, T)} \min_{s} \min_{\rho} U_M(s, \pi, \rho, T)$$

be the optimal expected $T$-step average return such policies guarantee, uniformly over start states and adversary policies. Let $p_1$ be a polynomial. Run R-max with input $T$ and a visit threshold $K_1$ that meets the source's accuracy requirement (after $K_1$ samples of an entry, all estimated transition probabilities are within $\varepsilon/(2N T R_{\max})$ of the true ones except with total probability at most $\delta/3$) and satisfies $K_1 \le p_1(N, k, T, R_{\max}/\varepsilon, \ln(1/\delta))$, as the source's own choice of $K_1$ does. Then there is a number of steps $t_0$, bounded by a polynomial in $N$, $k$, $T$, $1/\varepsilon$ and $1/\delta$ that depends only on $p_1$ and $R_{\max}$, and fixed in advance (a number of $T$-step phases chosen as a function of these parameters), such that, against any adversary behaviour and from any start state, with probability at least $1-\delta$ the average reward actually received by R-max over its first $t_0$ steps is at least $\mathrm{Opt}(\Pi_M(\varepsilon, T)) - 2\varepsilon$.

The source's Theorem 2 phrases the conclusion as attaining an expected return of $\mathrm{Opt}(\Pi_M(\varepsilon, T)) - 2\varepsilon$ within polynomially many steps; its proof (pp. 225–226) bounds the return actually received, allotting probability $\delta/3$ to realized exploitation returns falling short of their expectation, and that is the form stated here. The guarantee is for the prefix of $t_0$ steps; it is not claimed for every later prefix.

The source normalizes payoffs to $[0, R_{\max}]$ for a constant $R_{\max}$, so the polynomial may depend on it. The value $\mathrm{Opt}$ is written in the source without the start state and adversary; the uniform form above follows the source's convention $U_M(\pi) = \min_s U_M(s, \pi)$ for guaranteed values. The polynomial bound on $K_1$ matters: a larger threshold still meets the accuracy requirement but delays learning arbitrarily. The source's printed choice of $K_1$ is polynomial in these quantities, but its union bound counts $N k^2$ events where there are $N^2 k^2$ transition probabilities (see the algorithm page), so as printed it is not shown to meet the accuracy requirement; the theorem is therefore stated for any polynomially bounded threshold that meets it. The input $T$ can be removed by running the algorithm with $T = 1, 2, \dots$ in sequence. MDPs and repeated games are special cases (one adversary action, respectively one state).

## Depends on

- [Fixed-sum stochastic game](fixed-sum-stochastic-game.md)
- [R-max algorithm](r-max-algorithm.md)

## Proof depends on

- [Implicit Explore or Exploit Lemma](implicit-explore-or-exploit-lemma.md)
- [Simulation lemma for T-step average returns](simulation-lemma-for-t-step-average-returns.md)
- [Hoeffding's inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)
- [Azuma-Hoeffding inequality for adaptive processes with bounded conditional ranges](../../../../Probability/concentration-inequalities/adaptive-martingale-tail-bounds/azuma-hoeffding-bounded-conditional-ranges.md)

## Expansion

The proof compares three games: the true game $M$, the model $M'_L$ the agent uses, and an $\varepsilon/(2N T R_{\max})$-approximation $M'$ of $M$ whose induced game is $M'_L$. In each $T$-step phase the Implicit Explore or Exploit Lemma, applied to $M'$ and $M'_L$, gives either average reward within $\varepsilon/2$ of optimal or an unknown entry played with probability at least $\alpha/R_{\max}$, and the simulation lemma transfers this to $M$. Three failure events get probability $\delta/3$ each: inaccurate transition estimates at known entries (excluded by the choice of $K_1$, with a union bound over all $N^2 k^2$ transition probabilities); too few visits to unknown entries after polynomially many exploration attempts, each succeeding with probability at least $\alpha/R_{\max}$; and realized exploitation returns more than $\varepsilon/2$ below their expectation after polynomially many exploitation phases. Choosing the number of phases so that exploitation phases outweigh the at most polynomially many low-reward exploration phases, as in the source's overview (losses of $L$ learning phases are compensated by $D = L R_{\max}/\varepsilon$ further phases), gives the bound on the realized average reward over the first $t_0$ steps. The source bounds the last two with a Chernoff bound for independent bounded variables; since phases are chosen adaptively, the martingale form of that bound is the rigorous tool. The total number of $T$-step phases is polynomial in these quantities. Quantitative bounds for discounted MDPs are given by the PAC-MDP analysis of R-max.

## Sources

- R. I. Brafman and M. Tennenholtz, "R-max – A General Polynomial Time Algorithm for Near-Optimal Reinforcement Learning", *Journal of Machine Learning Research* 3 (2002), 213–231, [www.jmlr.org](https://www.jmlr.org/papers/volume3/brafman02a/brafman02a.pdf): Theorem 2 (Section 4, p. 220), the normalization of payoffs and the definitions of $U_M$ and $\Pi(\varepsilon, T)$ (Section 2, pp. 217–218), the proof (pp. 225–226) and the removal of the known mixing time (p. 227).
