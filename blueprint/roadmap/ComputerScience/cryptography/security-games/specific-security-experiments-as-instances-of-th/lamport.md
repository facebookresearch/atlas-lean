# Lamport one-time signature scheme

Let $X$ be finite and nonempty, $Y$ a type with decidable equality, $f \colon X \to Y$ and $\ell \in \mathbb{N}$. Lamport's one-time signature scheme for messages $m \in \{0,1\}^\ell$ (Katz and Lindell, Section 12.6.1):

- key generation draws a secret key $sk \colon \{0, \dots, \ell-1\} \times \{0,1\} \to X$ uniformly and sets the public key $pk(i, c) = f(sk(i, c))$;
- signing is deterministic: $\sigma_i = sk(i, m_i)$ for each position $i < \ell$;
- a pair $(m, \sigma)$ is accepted under $pk$ if and only if $f(\sigma_i) = pk(i, m_i)$ for every $i < \ell$.
