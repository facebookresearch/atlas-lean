# Follow the perturbed leader with a uniform cube perturbation: regret $2\sqrt{D R A T}$

Online linear optimization: a finite decision set $\alpha$ is represented by vectors $v_a \in \mathbb{R}^I$; in round $t$ a cost vector $\ell_t \in \mathbb{R}^I$ is revealed and decision $a$ costs $\langle v_a, \ell_t\rangle$. Follow the perturbed leader (FPL) with parameter $\varepsilon > 0$ draws $u$ uniformly from the cube $[0,1]^I$ and plays $\arg\min_a \langle v_a, \sum_{s<t}\ell_s + u/\varepsilon\rangle$ (ties broken by a fixed order). Suppose $\langle v_a - v_b, u\rangle \le D$ for all $a, b$ and $u \in [0,1]^I$, $\langle v_a - v_b, \ell_t\rangle \le R$ and $\sum_i|\ell_t(i)| \le A$ for all $t < T$. Then for every decision $a^*$,

$$
\mathbb{E}\Big[\sum_{t<T}\langle v_{a_t}, \ell_t\rangle\Big] \le \sum_{t<T}\langle v_{a^*}, \ell_t\rangle + \frac{D}{\varepsilon} + \varepsilon RAT,
$$

and $\varepsilon = \sqrt{D/(RAT)}$ gives regret at most $2\sqrt{DRAT}$. For $N$ experts with $[0,1]$ losses (basis vectors) this is $2\sqrt{NT}$.

## Proof sketch

For a fixed perturbation, FPL is FTRL with the linear regularizer $\langle v_a, u\rangle/\varepsilon$, so the be-the-leader lemma bounds its regret by $D/\varepsilon$ plus stability terms. Shifting the cumulative cost by $\ell_t$ shifts the leader regions by $\varepsilon\ell_t$ relative to the cube; by translation invariance of volume the probability that the leader changes is at most the volume of the cube minus its translate, at most $\varepsilon\sum_i|\ell_t(i)| \le \varepsilon A$, and a change costs at most $R$.

## Depends on

- [Follow the regularized leader](follow-the-regularized-leader.md)

## Proof depends on

- [Be-the-leader: FTRL regret is at most regularizer range plus stability](ftrl-be-the-leader-lemma.md)

## Sources

- Adam Kalai and Santosh Vempala, "Efficient Algorithms for Online Decision Problems", Journal of Computer and System Sciences, 2005.
- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4.
