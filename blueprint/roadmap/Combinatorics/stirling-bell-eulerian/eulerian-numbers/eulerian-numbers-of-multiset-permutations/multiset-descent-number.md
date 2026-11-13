# Descent number of a word

For a word $w = w_1 \cdots w_K$ of length $K$ over the alphabet
$\{0, 1, \dots, m-1\}$, the descent number of $w$ is one more than its number of descents:
$1 + \#\{j : 1 \le j < K,\ w_j > w_{j+1}\}$.

The extra $1$ follows the source convention, which also counts a descent at the end of the
word; in particular the empty word has descent number $1$.
