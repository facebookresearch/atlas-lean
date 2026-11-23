# Nu-lambda Pascal matrix with coefficients

Let $N$ and $n$ be natural numbers with
$n > 0$, let $\nu, \lambda \in \mathbb{C}$ and $\beta_0, \dots, \beta_{N-1} \in \mathbb{C}$.
An array $S = (S_{i,j})_{i,j \ge 0}$ of complex numbers, indexed from $0$, is a
$(\nu, \lambda)$-Pascal matrix of size $2n$ with coefficients $\beta$ when the following
hold: $S_{i,j} = 0$ whenever $i \ge 2n$ or $j \ge 2n$; $S_{i,j} = -S_{j,i}$ for all $i, j$;
$S_{2n-2,\,2n-1} = 1$; $S_{j,\,2n-1} = \sum_{t=0}^{N-1} \beta_t S_{j+t+1,\,2n-1}$ for every
$j < 2n - 2$; and $S_{i,j} = \lambda S_{i+1,j+1} + \nu (S_{i+1,j} + S_{i,j+1})$ for all
$i, j < 2n - 1$.

The definition also allows $N = 0$; then the sum is empty, so the entries $S_{j,\,2n-1}$
with $j < 2n - 2$ vanish. The intended coefficient families have $N > 0$.
