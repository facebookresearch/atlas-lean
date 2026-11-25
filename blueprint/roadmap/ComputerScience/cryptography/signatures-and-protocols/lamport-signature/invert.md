# Inverter built from a forger

Let $f : X \to Y$, let $A$ be a one-time forger for messages
of length $\ell$ with coins in $R$, and let $y \in Y$. The inverter's coins are a position $(i, b)$
with $i < \ell$ and $b \in \{0, 1\}$, a secret key
$sk : \{0, \dots, \ell - 1\} \times \{0, 1\} \to X$ and forger coins $r \in R$. It forms the
public key $pk$ with $pk(i, b) = y$ and $pk(j, c) = f(sk(j, c))$ for every other $(j, c)$, and
runs $A$ on $pk$ with coins $r$ to obtain the message $m$ whose signature $A$ requests. If
$m_i = b$ it fails. Otherwise it hands $A$ the signature $(sk(j, m_j))_{j < \ell}$ of $m$ under
$sk$ and obtains a forgery $(m', \sigma')$; it outputs $\sigma'_i$ if $m'_i = b$ and fails
otherwise.
