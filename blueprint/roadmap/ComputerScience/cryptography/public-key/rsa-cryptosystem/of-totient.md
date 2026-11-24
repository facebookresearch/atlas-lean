# RSA key from the totient condition

Given distinct primes $p$ and $q$ and natural
numbers $e$ and $d$ with $ed \equiv 1 \pmod{\varphi(pq)}$, where $\varphi$ is Euler's totient
function, this is the RSA key with primes $p$ and $q$, public exponent $e$ and private exponent
$d$. Its conditions $ed \equiv 1 \pmod{p - 1}$ and $ed \equiv 1 \pmod{q - 1}$ hold because
$\varphi(pq) = (p - 1)(q - 1)$.
