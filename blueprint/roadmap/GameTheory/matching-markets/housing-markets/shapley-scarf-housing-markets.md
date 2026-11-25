# Shapley-Scarf housing markets

A housing market has $n \ge 1$ agents, each owning one house, and strict preferences of each agent over all houses. An allocation is a
bijection from agents to houses. A nonempty coalition $T$ weakly blocks an allocation if some reallocation of $T$'s own houses among $T$
makes every member weakly better off and some member strictly better off; it strictly blocks it if it makes every member strictly better
off. The strict core is the set of allocations not weakly blocked by any coalition, and the weak core the set of allocations not strictly
blocked by any coalition; the strict core is contained in the weak core. The core of Shapley and Scarf is the weak core.

The inclusion can be strict even with strict preferences. Let agent $a_k$ own house $h_k$ for $k = 1, 2, 3$, with preferences
$a_1 : h_2 \succ h_1 \succ h_3$, $a_2 : h_1 \succ h_3 \succ h_2$ and $a_3 : h_1 \succ h_2 \succ h_3$. The allocation
$a_1 \mapsto h_2$, $a_2 \mapsto h_3$, $a_3 \mapsto h_1$ is in the weak core, since $a_1$ and $a_3$ already hold their first choices and
$a_2$ alone can only take back $h_2$. It is not in the strict core: the coalition $\{a_1, a_2\}$ weakly blocks it by exchanging its own
houses, which keeps $h_2$ for $a_1$ and gives $h_1$, the first choice of $a_2$, to $a_2$.

## Sources

- L. Shapley and H. Scarf, *On Cores and Indivisibility*, J. Math. Econ. 1 (1974), 23–37, §2, p. 25 (the market and its core). <https://rohitvaish.in/data/Papers/%5BShapley,Scarf%5D%20On%20Cores%20and%20Indivisibility.pdf>
- F. Brandt, V. Conitzer, U. Endriss, J. Lang and A. D. Procaccia (eds.), *Handbook of Computational Social Choice*, Cambridge University Press, 2016, §14.3.1, p. 347 (weak and strong blocking, the strict core and the weak core, after Roth and Postlewaite 1977). <https://www.cse.unsw.edu.au/~haziz/comsoc.pdf>
