# Garbling schemes and Yao's construction

A *projective garbling scheme* takes a clear circuit $C$ on $n$ input wires and samples three things: a public garbled circuit, a pair of labels for each input wire, and output decoding information. On a clear input $x$, the encoder selects label $x_i$ from the $i$th pair. The deterministic evaluator receives only the public circuit and these $n$ active labels. The scheme is *correct* if, for every $C$, every garbling in the support of this distribution and every $x$, decoding the evaluator's result gives $C(x)$.

In Yao's four-row construction, consider a topologically ordered circuit of binary Boolean gates with any number of designated outputs. Independently for each wire $w$, draw two independent uniform keys from a finite nonempty key space and a fair bit $r_w$. The label for bit $a$ is $L_w^a=(k_w^a,a\oplus r_w)$. Even if the key payloads coincide, the pointers on the two labels differ. For a gate with function $f$, incoming wires $u,v$ and output wire $w$, put

$$
\operatorname{Enc}_{k_u^a,k_v^b}(L_w^{f(a,b)})
$$

at address $(a\oplus r_u,b\oplus r_v)$, for all four pairs $(a,b)$. The public gate consists of these ciphertexts and its wiring, not the clear function. The active input pointers address precisely the row encrypted under the active keys. Right-key decryption therefore yields the active label for $f(a,b)$. The [active-label invariant](trace-garble-program.md) holds at every wire by induction over the gates, including at wires read by several later gates. At a designated output, XOR the active pointer with the decoder's bit $r_w$ to recover the clear output. This proves [functional correctness](yao-correct.md); it makes no claim about what the ciphertexts conceal.

## Sources

- M. Bellare, V. T. Hoang and P. Rogaway, *Foundations of Garbled Circuits*, ACM CCS 2012, pp. 784–796. In the [full version of 1 October 2012 (ePrint 2012/265)](https://eprint.iacr.org/2012/265), §3.1 gives the garbling-scheme syntax and correctness condition, and §3.2 defines projective input encoding. Section 5 introduces tweakable dual-key ciphers. Garble1 (§5.1, Fig. 7) indexes four rows by the incoming token types and makes the output token's type equal to its clear bit, so its decoding data is empty. The construction above instead uses an untweaked row cipher and supplies a pointer mask for each designated output.
- R. Pass and A. shelat, *A Course in Cryptography*, 2010, [§§6.2.1–6.2.3](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf): wire keys and four encrypted rows. These notes shuffle the rows and try decryptions, rather than indexing by pointer bits.
- D. Evans, V. Kolesnikov and M. Rosulek, *A Pragmatic Introduction to Secure Multi-Party Computation*, Foundations and Trends in Privacy and Security 2(2–3), 2018, [§3.1.1](https://securecomputation.org/): point-and-permute. The explicit protocol in Fig. 3.1 uses an encrypted output table; the decoding information above is just the zero-label pointer at each output.
