# Probability of a derived-allele configuration

Let $n$ be a natural number and $q \in \mathbb{R}^n$. For a configuration $x \in \{0, 1\}^n$ ($x_i = 1$ when haplotype $i$ carries the derived allele), put

$$\pi_q(x) = \prod_{i=1}^{n} \begin{cases} q_i & x_i = 1,\\ 1 - q_i & x_i = 0. \end{cases}$$

For $q \in [0, 1]^n$ this is the probability of $x$ when haplotype $i$ is sampled independently and carries the derived allele with probability $q_i$; the definition applies to arbitrary real $q$.
