# Duality formula for binary expansions without adjacent ones

For $x \in \mathbb{N}$ let
$z(x)$ be the number of $n < x$ whose binary expansion has no two adjacent digits equal to $1$.
For a finite set $A \subseteq \mathbb{N}$, put $\bar A = A$ if there is no $j$ with
$j, j + 1 \in A$, and otherwise $\bar A = \{k \in A : k \ge j\}$, where $j$ is the largest index
with $j, j + 1 \in A$. Then $z\bigl(\sum_{k \in A} 2^k\bigr) = \sum_{k \in \bar A} F_{k+2}$,
where $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = F_{n+1} + F_n$ are the Fibonacci numbers.

## Sources

- Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25, Lemma 2.
