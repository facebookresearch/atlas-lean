# Holding times of Kingman's coalescent

Let $\mu$ be a measure on a measurable space $\Omega$ and let $n$ be a natural number. Kingman holding times for a sample of size $n$ under $\mu$ are real-valued functions $T_k$ on $\Omega$, one for each natural number $k$, such that

- for each $2 \le k \le n$, the law of $T_k$ under $\mu$ is the exponential distribution with rate $\binom{k}{2}$ (in particular $T_k$ is $\mu$-almost everywhere measurable);
- the functions $T_2, \dots, T_n$ are mutually independent under $\mu$.

The values $T_k$ for $k < 2$ or $k > n$ are unconstrained. In the coalescent, $T_k$ is the time, in units of $2N$ generations, during which the genealogy of the sample has exactly $k$ lineages. When $n \ge 2$, the first condition forces $\mu$ to be a probability measure.
