# Cost-instrumented computations

Running-time statements for algorithms are often made in a cost-instrumented style. An algorithm is written so that it returns its result together with a cost annotation, usually a natural number counting operations: returning a value adds no cost, running one step after another adds their costs, and an explicit charge records the cost of a primitive step. Correctness claims are then stated about the returned result and cost claims about the accumulated annotation, as a function of the input size for worst-case bounds.

The charges are part of the algorithm's text and are not checked against a machine model, so every such statement has to say which cost model it uses: which operations are charged one unit (for example comparisons or arithmetic operations), which are free, and whether recursive calls are charged. Bounds proved for different cost models are not comparable without a translation between the models.

## Sources

- N. A. Danielsson, "Lightweight semiformal time complexity analysis for purely functional data structures", *Proceedings of the 35th ACM POPL*, 2008, the reference given by the formal development for this design (a monad that pairs results with trusted, user-annotated costs)
