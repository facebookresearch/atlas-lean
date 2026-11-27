# Cross-term identity for folding relaxed R1CS

Let $(E_1,u_1,x_1)$, $(E_2,u_2,x_2)$ be relaxed R1CS instances with witnesses $W_1,W_2$, and $z_i=(W_i,u_i,x_i)$. Define the cross term

$$
T=Az_1\circ Bz_2+Az_2\circ Bz_1-u_1Cz_2-u_2Cz_1\in\mathbb{F}^{m}.
$$

For any $r\in\mathbb{F}$ put $z=z_1+rz_2$, $u=u_1+ru_2$ and $E=E_1+rT+r^{2}E_2$. Then

$$
Az\circ Bz-u\cdot Cz=\bigl(Az_1\circ Bz_1-u_1Cz_1\bigr)+rT+r^{2}\bigl(Az_2\circ Bz_2-u_2Cz_2\bigr),
$$

so if both inputs are satisfying, $(E,u,x_1+rx_2)$ is satisfied by $W_1+rW_2$.

## Proof sketch

Expand $A(z_1+rz_2)\circ B(z_1+rz_2)$ by bilinearity of the Hadamard product into $Az_1\circ Bz_1+r(Az_1\circ Bz_2+Az_2\circ Bz_1)+r^{2}Az_2\circ Bz_2$, and expand $(u_1+ru_2)C(z_1+rz_2)$ similarly. Collecting powers of $r$ gives the displayed identity, and substituting $Az_i\circ Bz_i-u_iCz_i=E_i$ yields the folded relation.

## Depends on

- [Relaxed R1CS instances with slack vector and scalar](relaxed-r1cs.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, Ioanna Tzialla, "Nova: Recursive Zero-Knowledge Arguments from Folding Schemes", CRYPTO (2022), IACR ePrint 2021/370.
