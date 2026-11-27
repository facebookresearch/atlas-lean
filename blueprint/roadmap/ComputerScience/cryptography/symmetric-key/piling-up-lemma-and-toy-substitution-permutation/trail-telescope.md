# Trail error bits telescope to boundary parities

Let $m, r \in \mathbb{N}$, and for every round index $i \in \mathbb{N}$ let $k_i \in \mathrm{Bool}^m$ be a key, $S_i : \mathrm{Bool}^m \to \mathrm{Bool}^m$ an arbitrary map, $\pi_i$ a permutation of $\{0, \dots, m-1\}$, and $u_i, x_i \in \mathrm{Bool}^m$ a mask and a state. Assume the states follow the [SPN round](spn-round.md) for every $i$:

$$
x_{i+1} = \mathrm{spnRound}(k_i, S_i, \pi_i, x_i).
$$

Define the round [error bits](err-bit.md)

$$
e_i = \mathrm{errBit}\bigl(u_i,\ x_i,\ \mathrm{transportMask}(u_{i+1}, \pi_i),\ S_i(x_i \oplus k_i)\bigr) = \mathrm{parity}(u_i, x_i) \oplus \mathrm{parity}\bigl(\mathrm{transportMask}(u_{i+1}, \pi_i),\ S_i(x_i \oplus k_i)\bigr),
$$

using the [transported mask](transport-mask.md) and the [mask parity](parity.md). Then the exclusive or of $e_0, \dots, e_{r-1}$ (a right fold starting from false) equals the exclusive or of the two boundary parities, with no key term:

$$
e_0 \oplus \cdots \oplus e_{r-1} = \mathrm{parity}(u_0, x_0) \oplus \mathrm{parity}(u_r, x_r).
$$

This includes $r = 0$, where both sides are false.
