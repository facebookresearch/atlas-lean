# Charnov's marginal value theorem

Charnov's (1976) rule is that "the predator should leave the patch it is presently in when the marginal capture rate in the patch drops to the average capture rate for the habitat"; graphically, the optimal residence time is where the line from the point $(-\tau, 0)$, one mean travel time before arrival, is tangent to the gain curve (Stephens and Krebs 1986, Chapter 3). In Charnov's multi-patch form: a forager meets patches of types $i = 1, \dots, k$ with probabilities $p_i > 0$, spends a mean travel time $\tau > 0$ between patches, and gains $g_i(t)$ from residence time $t$ in a patch of type $i$, where each $g_i : [0, \infty) \to [0, \infty)$ is differentiable, increasing and concave with $g_i(0) = 0$. Its long-run intake rate is

$$E(t_1, \dots, t_k) = \frac{\sum_i p_i\, g_i(t_i)}{\tau + \sum_i p_i t_i}.$$

Since $\partial_{t_i} E = p_i\,(g_i'(t_i) - E)/(\tau + \sum_j p_j t_j)$, every maximizer with all $t_i^* > 0$ satisfies $g_i'(t_i^*) = E^* = E(t^*)$ for every $i$: the marginal gain in each patch equals the maximal average rate. Conversely, concavity makes this condition sufficient: $E \le E^*$ is equivalent to $\sum_i p_i (g_i(t_i) - E^* t_i) \le E^*\tau$, and the left side is a concave function of $(t_i)$ maximized where $g_i' = E^*$; strict concavity makes the maximizer unique.

## Expansion

1. The model: patch types, gain functions and the long-run rate $E$ as a ratio of expectations (renewal-reward theorem).
2. The first-order conditions from the partial derivatives of $E$.
3. Sufficiency under concavity by the reformulation $\sum_i p_i(g_i(t_i) - E^* t_i) \le E^* \tau$.
4. Uniqueness under strict concavity, and boundary maximizers (patch types not worth entering).

## Sources

- Original result: E. L. Charnov, Optimal foraging, the marginal value theorem, Theor. Popul. Biol. 9 (1976), 129–136. <https://doi.org/10.1016/0040-5809(76)90040-X>
- D. W. Stephens and J. R. Krebs, *Foraging Theory*, Princeton University Press, 1986, Chapter 3.
- V. Calcagno, L. Mailleret, É. Wajnberg and F. Grognard, How optimal foragers should respond to habitat changes: a reanalysis of the Marginal Value Theorem, J. Math. Biol. 69 (2014). <https://doi.org/10.1007/s00285-013-0734-y>
