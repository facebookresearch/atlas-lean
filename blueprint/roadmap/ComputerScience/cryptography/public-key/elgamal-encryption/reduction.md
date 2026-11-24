# DDH distinguisher from an ElGamal eavesdropper

Let $G$ be a finite commutative group and
let $A$ be an eavesdropping adversary with coins in a finite nonempty type $R$. The distinguisher
built from $A$ takes three elements $X, Y, Z \in G$ and coins consisting of $r \in R$ and a bit
$b$. It lets $A$ choose messages $(m_0, m_1)$ from the public key $X$ and the coins $r$, gives $A$
the public key $X$, the ciphertext $(Y, Z m_b)$ and the coins $r$, where $m_b$ is $m_1$ if $b$ is
true and $m_0$ otherwise, and outputs true exactly when the guess of $A$ equals $b$.
