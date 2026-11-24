# Cost-instrumented computations

A cost-instrumented computation with cost values in $T$ and results in $\alpha$ is a pair $(\mathrm{ret}, \mathrm{time})$ with $\mathrm{ret} \in \alpha$ and $\mathrm{time} \in T$, usually with $T = \mathbb{N}$ counting operations. Returning a value costs nothing, $\mathrm{pure}(a) = (a, 0)$; sequencing adds costs, so if $m = (a, t)$ and $f(a) = (b, t')$ then $m \mathbin{>\!\!>\!\!=} f = (b, t + t')$; and $\mathrm{tick}(c) = ((), c)$ charges $c$ units. When $T$ is an additive monoid these operations form a lawful monad. Correctness is stated about $\mathrm{ret}$ and cost about $\mathrm{time}$. The charges are written into the program and are not checked against a machine, so each algorithm fixes its cost model: which operations cost one unit (for example comparisons or arithmetic operations), which are free, and whether recursive calls are charged. Worst-case bounds compare $\mathrm{time}$ as a function of the input size.

## Sources

- N. A. Danielsson, "Lightweight semiformal time complexity analysis for purely functional data structures", *Proceedings of the 35th ACM POPL*, 2008, the reference given by the formal development for this design (a monad that pairs results with trusted, user-annotated costs)
