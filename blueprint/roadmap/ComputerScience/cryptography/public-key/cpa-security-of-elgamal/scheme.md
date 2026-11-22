# ElGamal as a public-key encryption scheme

For a finite commutative group $G$, an element $g \in G$ and an integer $q \ge 1$, ElGamal (Katz and
Lindell, Construction 11.16) is the public-key encryption scheme that draws a uniform secret key
$x \in \mathbb{Z}/q$ and publishes $h = g^x$; encrypts $m \in G$ by drawing a uniform
$y \in \mathbb{Z}/q$ and outputting $(g^y, h^y m)$; and decrypts $(c_1, c_2)$ with $x$ to
$c_2 (c_1^x)^{-1}$, never failing. Here, for $u \in G$ and $a \in \mathbb{Z}/q$, $u^a$ means
$u^{\bar a}$, where $\bar a$ is the representative of $a$ in $\{0, \dots, q - 1\}$; no condition on
the order of $g$ is assumed.
