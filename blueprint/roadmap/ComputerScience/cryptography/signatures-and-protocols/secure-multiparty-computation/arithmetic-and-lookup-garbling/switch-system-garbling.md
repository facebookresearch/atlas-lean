# Garbling switch systems for arithmetic circuits

A *switch system* (Heath) is a system of constraints on wires carrying values modulo powers of two $2^k$, built from gates: a *switch* with control wire $\mathrm{ctrl} \in \mathbb{Z}_2$ and data wires $x, y \in \mathbb{Z}_{2^k}$ imposes $\mathrm{ctrl} = 0 \Rightarrow x = y$; a *join* imposes $x = y$; an *affine gate* imposes $f(x) = y$ for an affine map $f$; a *modulus gate* imposes $y = [x]_{2^k}$ for $x \in \mathbb{Z}_{2^{k+c}}$; and a *division gate* imposes $y = [x/2^c]_{2^k}$ for $x \in \mathbb{Z}_{2^{k+c}}$ known to be a multiple of $2^c$. It is *legal* if every input determines a unique satisfying assignment, and its *controls* on an input are the values of all switch control wires. A *randomized* switch system $(S, D)$ also takes auxiliary inputs $r$ drawn from $D$, and a family of legal randomized switch systems is *oblivious* if a simulator, given only the security parameter, outputs a distribution statistically close to the controls on $(x; r)$, $r \leftarrow D$, for every input $x$. In Heath's garbling, the label of value $w$ on a wire is $K_w^0 + w\Delta$ for one global offset $\Delta$ with low bit $1$; affine, modulus and division gates are free; a switch reveals its control bit (the low bit of the control label) and sets $K_y^0 = K_x^0 + H(K_{\mathrm{ctrl}}^0, \mathrm{gid})$ with a gate-specific nonce $\mathrm{gid}$, carrying no ciphertext; and each join sends the difference $K_y^0 - K_x^0$ of its zero labels, so the material is about $\lambda$ times the total width of joined wires. Then (i) for a legal system and an input $x$, garbled evaluation tracks propagation: every wire whose value propagation from $x$ finds receives its active label, so every output wire on which propagation finds a value decodes to that value; (ii) if the hash is circular correlation robust and the family is oblivious, the garbling is oblivious: the garbled material together with the encoded input is computationally indistinguishable from a simulation that does not depend on $x$. Without obliviousness of the family, the revealed control bits can leak the input.

## Proof sketch

(i) Induct over the order in which evaluation solves gates: affine, modulus and division gates preserve the affine label invariant, a switch with control $0$ connects its data labels through the hash value, and a join through the sent difference. (ii) The simulator draws the controls from the family's simulator; for a switch with control $1$ the hash value at the inactive control label stays unknown to the evaluator, which correlation robustness replaces by a uniform value, so the switch's output label is simulated by a uniform string, and join differences are then computed from simulated labels.

## Depends on

- [Affine wire labels for arithmetic garbling](affine-wire-labels.md)
- [Circular correlation robust hash functions](../garbling-scheme-security/circular-correlation-robustness.md)

## Sources

- David Heath, "Efficient Arithmetic in Garbled Circuits", Advances in Cryptology – EUROCRYPT 2024, 2024.
