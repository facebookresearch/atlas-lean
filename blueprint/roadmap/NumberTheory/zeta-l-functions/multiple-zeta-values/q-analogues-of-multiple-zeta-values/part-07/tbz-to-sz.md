# The map from TBZ words to SZ indices

Words in the letters $\bar{1}$ and $k \in \mathbb{N}$
are sent to formal $\mathbb{Q}$-linear combinations of finite sequences of natural numbers (SZ
indices) letter by letter: the empty word goes to the empty index with coefficient $1$, and a
word $x w$ with first letter $x$ goes to the image of $w$ with a new first entry prepended to each
index, where $\bar{1}$ contributes the entry $1$ and a letter $k$ contributes the sum of the two
terms obtained with the entries $k$ and $k - 1$ (subtraction truncated at $0$, so the letter $0$
gives the entry $0$ with coefficient doubled). This is the map $U_{\mathrm{TBZ}}$ on words.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Proposition 9 (i) (the map `U_TBZ`).
