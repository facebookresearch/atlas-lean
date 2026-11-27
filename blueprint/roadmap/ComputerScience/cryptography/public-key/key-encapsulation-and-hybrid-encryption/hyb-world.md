# Intermediate worlds of the hybrid proof

For bits $b$ and $u$, the hybrid world draws $(pk, sk)$, the adversary's coins and an encapsulation
$(k, e)$. It takes the data-encapsulation key to be $k$ if $u = 0$ and a uniform key if $u = 1$,
encrypts the adversary's message $m_b$ under that key as $c$, and outputs the adversary's guess on
$(e, c)$.
