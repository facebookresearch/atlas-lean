# Halfspaces over infinite domains are not privately learnable

For every $d \ge 2$, the class of halfspaces in $\mathbb{R}^d$ (and already the class of thresholds on $\mathbb{R}$ or on $\mathbb{N}$) is not PAC learnable by any $(0.1, O(1/(n^2\log n)))$-differentially private algorithm with a finite number of samples, although its VC dimension is $d+1$. Over the finite grid $\{1, \dots, N\}^d$, the private sample complexity of halfspaces must grow with $N$, at least as $\Omega(\log^* N)$.

## Proof sketch

Halfspaces contain thresholds (restrict to a line), and thresholds on an infinite ordered domain have infinite Littlestone dimension; on the grid $\{1,\dots,N\}$ they have Littlestone dimension $\lfloor\log_2 N\rfloor$. The $\Omega(\log^* d)$ lower bound for private learning in terms of the Littlestone dimension then gives non-learnability over infinite domains and the $\log^* N$ growth over grids.

## Depends on

- [Private PAC learners and their sample complexity](private-pac-learner.md)

## Proof depends on

- [Private learning requires log-star of the Littlestone dimension samples](private-learning-requires-log-star-littlestone.md)
- [Large Littlestone dimension forces large threshold subclasses](littlestone-dimension-contains-thresholds.md)

## Sources

- N. Alon, R. Livni, M. Malliaris, S. Moran, "Private PAC Learning Implies Finite Littlestone Dimension", STOC (2019), arXiv:1806.00949.
