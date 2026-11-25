# The PRF distinguisher built from a CPA adversary

Let $X$ and $R$ be sets, $Y$ an additive
commutative group, $q$ a natural number and $A$ a CPA adversary with coins in $R$ against an
encryption oracle that takes messages in $Y$ and returns ciphertexts in $X \times Y$. With its own
coins $(\rho, r_s, b, r)$, where $\rho \colon \{0, \dots, q - 1\} \to X$, $r_s \in X$, $b$ is a bit
and $r \in R$, and with oracle access to a function $O \colon X \to Y$, the distinguisher runs the
algorithm $A$ assigns to $r$. It answers the encryption query with index $i$, counting from $0$
across both phases, for a message $m$ by querying $O$ at $\rho_i$ and returning
$(\rho_i, O(\rho_i) + m)$. When the first phase outputs messages $(m_0, m_1)$, it queries $O$ at
$r_s$ and gives the second phase the challenge ciphertext $(r_s, O(r_s) + m_b)$, where $m_b$ is
$m_1$ if $b$ is true and $m_0$ otherwise. It outputs true exactly when the adversary's guess
equals $b$, where an adversary that asks more than $q$ encryption queries is stopped and guesses
false.
