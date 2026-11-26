# Finite-dimensional convergence for martingale arrays

On a probability space, let $(X_{n,k})$ be an array whose row partial sums $\sum_{j<k} X_{n,j}$ are martingales for filtrations $(\mathcal F_{n,k})_k$, and let $r_n$ be row lengths such that McLeish's conditions hold:

- $\mathbb{E}[\max_{k < r_n} X_{n,k}^2]$ is eventually bounded;
- $\max_{k < r_n} |X_{n,k}| \to 0$ in probability.

Let $\iota$ be a linearly ordered time axis, $N_n : \iota \to \mathbb{N}$ monotone with $N_n(s) \le r_n$ (for example $N_n(s) = \lfloor n s\rfloor$ on $[0, 1]$ with $r_n = n$), and $S_n(s) = \sum_{k < N_n(s)} X_{n,k}$. Suppose that for every time $s$ the realized quadratic variation $\sum_{k < N_n(s)} X_{n,k}^2$ tends to $A(s)$ in probability. Let $Z = (Z_s)_{s \in \iota}$ be a family of random variables on a probability space, each $Z_s$ measurable, whose finite linear combinations $\sum_{s \in I} c_s Z_s$ are centered Gaussian with variance the nonnegative part of $\sum_{s,u \in I} c_s c_u A(\min(s,u))$. Then for every finite set of times $I$, $(S_n(s))_{s \in I}$ converges in distribution to $(Z_s)_{s \in I}$. Only finite-dimensional laws are compared: with $A$ the identity on $[0, 1]$, $Z$ has the same finite-dimensional laws as a Brownian motion, and in general the same finite-dimensional laws as $W \circ A$ for a Brownian motion $W$; no path property of $Z$ follows.

The proof applies the Cramér–Wold device to the weighted array $a_{n,k} X_{n,k}$ with $a_{n,k} = \sum_{s \in I} c_s \mathbf 1\{k < N_n(s)\}$.

## Sources

- D. L. McLeish, "Dependent central limit theorems and invariance principles", Annals of Probability 2(4) (1974), 620–628, Theorem (3.2), finite-dimensional part of the proof, with a general variance function $A$ in place of $t$.
