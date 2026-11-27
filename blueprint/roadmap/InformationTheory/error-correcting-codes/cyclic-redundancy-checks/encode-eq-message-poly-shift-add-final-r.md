# Polynomial CRC codeword from the unreflected serial register

Let $r \in \mathbb{N}$, let $g \in \mathbb{F}_2[X]$ be a monic polynomial of degree $r$, and let $t$ be the width-$r$ taps word formed from the low coefficients of $g$. For every finite MSB-first payload $B \in \{0, 1\}^*$, the polynomial CRC encoding of the message polynomial $m(B)$ with generator $g$ equals the shifted message plus the binary polynomial of the final unreflected serial CRC register:

$$\mathrm{encode}_g(m(B)) = m(B) X^r + P_{\mathrm{final}_{r, t}(B)} \in \mathbb{F}_2[X],$$

since subtraction and addition coincide in characteristic $2$.
