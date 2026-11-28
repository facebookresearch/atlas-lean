# The black-white pebble game

The black-white pebble game on a DAG with a unique sink places black pebbles on vertices whose predecessors are pebbled and white pebbles anywhere, removes white pebbles once predecessors are pebbled, and ends with one black pebble on the sink; its price is the least maximal number of pebbles used.

Let $G$ be a directed acyclic graph with a unique sink $z$. A **configuration** is a pair $\mathbb{P} = (B, W)$ of disjoint sets of black and white pebbled vertices. The rules are:

1. if all immediate predecessors of an empty vertex $v$ carry pebbles, a black pebble may be placed on $v$ (in particular on any source);
2. a black pebble may be removed from any vertex at any time;
3. a white pebble may be placed on any empty vertex at any time;
4. if all immediate predecessors of a white-pebbled vertex $v$ carry pebbles, the white pebble on $v$ may be removed (in particular from any source).

A **complete black-white pebbling** of $G$ is a sequence $\mathcal{P} = \{\mathbb{P}_0, \dots, \mathbb{P}_\tau\}$ with $\mathbb{P}_0 = (\emptyset, \emptyset)$ and $\mathbb{P}_\tau = (\{z\}, \emptyset)$ in which each configuration follows from the previous one by one rule. Its **time** is $\tau$ and its **space** is $\max_{0 \le t \le \tau} |B_t \cup W_t|$. The **black-white pebbling price** $\mathit{BW}\text{-}\mathit{Peb}(G)$ is the minimum space of a complete black-white pebbling of $G$; restricting to $W_t = \emptyset$ for all $t$ gives black pebblings and the **black pebbling price** $\mathit{Peb}(G)$.

## Expansion

Black pebbles model values computed and stored, white pebbles model guesses that must later be verified. Pebbling formulas of DAGs encode the game, and the time-space trade-offs of pebblings (for example those of Lengauer and Tarjan, and of Carlson and Savage) are what substitution theorems transfer to resolution length-space trade-offs. There are DAGs on $n$ vertices of fan-in $2$ whose black-white pebbling price is $\Theta(n / \log n)$ (Gilbert and Tarjan).

## Depends on

None.

## Proof depends on

None.

## Sources

- J. Nordström, "Pebble games, proof complexity, and time-space trade-offs", *Logical Methods in Computer Science* 9(3:15), 2013, doi:10.2168/LMCS-9(3:15)2013, arXiv:1307.3913v3 (Definition 2.10, Section 2.3).
