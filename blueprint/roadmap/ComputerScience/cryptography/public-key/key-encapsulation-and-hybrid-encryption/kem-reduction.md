# KEM adversary from a public-key adversary

Let the data-encapsulation mechanism encrypt $m$ under $k$ as $E(k, m, s)$ for $s$ drawn from $\rho$.
From an eavesdropping adversary $A$ against the hybrid scheme and a fixed bit $b$, the KEM adversary
draws the coins of $A$ and a sample $s$ of $\rho$. On a public key, an encapsulation $e$ and a
candidate key $k$, it encrypts the message $m_b$ that $A$ chooses as $E(k, m_b, s)$ and returns the
guess of $A$ on the ciphertext $(e, E(k, m_b, s))$.
