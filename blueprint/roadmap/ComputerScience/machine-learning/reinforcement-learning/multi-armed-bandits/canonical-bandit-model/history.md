# History of a bandit interaction

A history of $t$ rounds of a $k$-armed bandit is the tuple $(a_1, x_1, \dots, a_t, x_t)$ of the arms chosen and
the rewards received, an element of $(\{1, \dots, k\} \times \mathbb{R})^t$. It carries the $t$-fold product of the
$\sigma$-algebra on arm–reward pairs, the product of the discrete $\sigma$-algebra on the arms and the Borel
$\sigma$-algebra on $\mathbb{R}$. In the formal statement, arms and rounds
are counted from $0$: the arm $a$ is stored as $a - 1$, and a history is a map from $\{0, \dots, t-1\}$ to
$\{0, \dots, k-1\} \times \mathbb{R}$ whose value at $s$ is the pair $(a_{s+1} - 1, x_{s+1})$.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Section 4.6 (the spaces $\Omega_t = ([k] \times \mathbb{R})^t$ with their Borel $\sigma$-algebras). <https://tor-lattimore.com/downloads/book/book.pdf>
