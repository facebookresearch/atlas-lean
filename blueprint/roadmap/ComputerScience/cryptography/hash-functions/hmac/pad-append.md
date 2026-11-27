# Padding a concatenation

For every block length $n$, length-field width $L$ and bit strings $u$, $m$, the strengthened padding of $u \,\|\, m$ is $u$ followed by the [padding of $m$ behind a $|u|$-bit prefix](pad-tail.md):

$$
\mathrm{pad}_{n,L}(u \,\|\, m) = u \,\|\, \Bigl(m \,\|\, 1 \,\|\, 0^{z(|u| + |m|)} \,\|\, \langle |u| + |m| \rangle_L\Bigr),
$$

with $z$ and $\langle \cdot \rangle_L$ as on that page.
