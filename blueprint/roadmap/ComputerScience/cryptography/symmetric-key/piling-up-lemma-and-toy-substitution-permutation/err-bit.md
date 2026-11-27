# Err Bit

For a width $m \in \mathbb{N}$ and four arbitrary words $u, x, a, s \in \mathrm{Bool}^m$, the error bit is the exclusive or of two [mask parities](parity.md):

$$
\mathrm{errBit}(u, x, a, s) = \mathrm{parity}(u, x) \oplus \mathrm{parity}(a, s),
$$

where $\mathrm{parity}(u, x)$ is the exclusive or of the bits $x_i$ over the indices $i$ with $u_i$ true. The definition involves no substitution or transport; in the [trail telescope](trail-telescope.md) the second pair is instantiated with a transported mask and a substitution output.
