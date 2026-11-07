# Golden mean flips

Encode a finite base phi expansion with digits $0$ and $1$ by the
finite set of positions of its digits $1$. An expansion $T$ arises from an expansion $S$ by a
golden mean flip $100 \to 011$ when there is a position $i \in S$ with $i - 1 \notin S$ and
$i - 2 \notin S$ such that $T = (S \setminus \{i\}) \cup \{i - 1, i - 2\}$: the digit $1$ at
position $i$ is replaced by digits $1$ at positions $i - 1$ and $i - 2$, which were $0$.

## Sources

- Michel Dekking and Ad van Loon, *Counting Base Phi Representations*, Fibonacci Quarterly 62 (2024), Sections 1 and 2 (the map `T_i`).
