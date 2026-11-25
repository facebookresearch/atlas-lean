# Finite-dimensional distributions of a finite Markov chain

Let `P` be a real matrix indexed by a finite set `S`, `a ∈ S` a starting state, `k ∈ ℕ`, times
`m_0, …, m_k ∈ ℕ` and states `x_0, …, x_k ∈ S`. The value is

`P^(m_0)(a, x_0) ∏_{i < k} P^(m_{i+1} - m_i)(x_i, x_{i+1})`,

where the natural-number difference `m_{i+1} - m_i` is truncated at `0`, so a factor with
`m_{i+1} < m_i` is the entry of the identity matrix (`1` if `x_i = x_{i+1}` and `0` otherwise). When
`P` is a stochastic matrix and `m_0 ≤ m_1 ≤ ⋯ ≤ m_k`, it is, by the Markov property, the probability
that the Markov chain with transition matrix `P` started from `a` at time `0` is at `x_i` at time
`m_i` for every `i`.
