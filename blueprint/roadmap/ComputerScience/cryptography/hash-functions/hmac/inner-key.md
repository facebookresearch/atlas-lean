# Derived inner and outer keys

For a compression function $h : S \times \{0,1\}^n \to S$, an initial value $\mathrm{iv}$, a key $k \in \{0,1\}^n$ and a pad block $p \in \{0,1\}^n$, the derived key is $h(\mathrm{iv}, k \oplus p)$. With $p = \mathrm{ipad}$ it is the inner key $k_{\mathrm{in}} = h(\mathrm{iv}, k \oplus \mathrm{ipad})$, and with $p = \mathrm{opad}$ the outer key $k_{\mathrm{out}} = h(\mathrm{iv}, k \oplus \mathrm{opad})$; the two pads are arbitrary blocks, and the two keys are the same construction with different pads.
