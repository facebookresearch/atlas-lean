# Garbling schemes and Yao's construction

A *garbling scheme* maps a Boolean circuit $C$ with $n$ input wires to a garbled circuit $\tilde C$, a pair of labels $(L^0_i, L^1_i)$ for each input wire $i$, and decoding information, together with a deterministic evaluation algorithm; it is *correct* if for every input $x$, evaluating $\tilde C$ on $L^{x_1}_1, \dots, L^{x_n}_n$ and decoding yields $C(x)$. In Yao's construction every wire $w$ receives two random labels and a select bit with complementary values on its two labels; each gate $g$ with input wires $u, v$ and output wire $w$ is garbled as four ciphertexts $\mathrm{Enc}_{L^a_u, L^b_v}(L^{g(a,b)}_w)$ under a dual-key cipher, placed in rows indexed by the select bits of $L^a_u$ and $L^b_v$ (point-and-permute).

## Sources

- R. Pass and A. shelat, *A Course in Cryptography*, lecture notes, Cornell University, 2010, <https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf>
- D. Evans, V. Kolesnikov and M. Rosulek, *A Pragmatic Introduction to Secure Multi-Party Computation*, Foundations and Trends in Privacy and Security 2(2–3), 2018, <https://securecomputation.org/>
