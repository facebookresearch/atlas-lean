# ElGamal eavesdropping experiment

Let $G$ be a commutative group, $g \in G$ and $q \ge 1$.
For an eavesdropping adversary $A$ with coins in a finite nonempty type $R$, the experiment draws
$x, y \in \mathbb{Z}/q$, coins $r \in R$ and a bit $b$ independently and uniformly. It sets the
public key $h = g^x$, lets $A$ choose messages $(m_0, m_1)$ from $h$ and $r$, and gives $A$ the
key $h$, the ElGamal ciphertext $(g^y, h^y m_b)$ and the coins $r$, where $m_b$ is $m_1$ if $b$
is true and $m_0$ otherwise; powers use the value of the exponent in $\{0, \dots, q - 1\}$. The
experiment outputs the distribution of the bit "the guess of $A$ equals $b$".
