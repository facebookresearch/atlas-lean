# Winning the Lamport one-time forgery game

Let $X$ be a nonempty finite set, $Y$ a set
with decidable equality, $f : X \to Y$ a function, and $\ell$ a message length; messages are bit
strings $m = (m_0, \dots, m_{\ell-1})$. A one-time forger $A$ with random coins from a nonempty
finite set $R$ wins against a secret key $sk$, which assigns $sk(i, b) \in X$ to each position
$i < \ell$ and bit $b$, with coins $r \in R$ when the following holds. Let $pk$ be the public key
of $sk$, given by $pk(i, b) = f(sk(i, b))$; let $m$ be the message that $A$ chooses from $pk$ and
$r$; and let $(m', \sigma')$ be the message and signature that $A$ outputs from $pk$, the
signature $i \mapsto sk(i, m_i)$ of $m$ under $sk$, and $r$. Then $m' \ne m$, and $\sigma'$ is a
valid signature on $m'$ for $pk$: $f(\sigma'_i) = pk(i, m'_i)$ for every $i < \ell$.
