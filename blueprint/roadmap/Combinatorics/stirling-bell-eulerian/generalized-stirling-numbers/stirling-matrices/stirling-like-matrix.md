# Stirling-like matrix

For a sequence $\alpha \colon \mathbb{N} \to \mathbb{Q}$ and
$n \in \mathbb{N}$, the Stirling-like matrix $S_\alpha(n)$ is the $n \times n$ rational matrix,
with rows and columns indexed by $1, \dots, n$, whose $(i, j)$ entry is $S_{i,j}$, where
$S_{1,j} = \alpha_{j-1}$ for $j \ge 1$, $S_{i,1} = \alpha_0$ for $i \ge 2$, and
$S_{i,j} = S_{i-1,j-1} + j \, S_{i-1,j}$ for $i, j \ge 2$.
