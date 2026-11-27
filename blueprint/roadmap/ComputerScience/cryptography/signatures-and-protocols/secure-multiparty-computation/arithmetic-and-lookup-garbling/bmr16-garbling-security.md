# Correctness and privacy of BMR16 mixed-modulus garbling

For BMR16 garbling of mixed-modulus circuits (additions, multiplications by units and projection gates): for every hash, offsets $(\Delta_m)$ and zero labels, evaluating the garbled circuit on encoded inputs yields the active label of every wire, and decoding returns the circuit's output unless, for some output wire $i$ with active label $Y_i$ and some other value $k$, the decoding hash $H(\mathrm{out} \Vert i \Vert k, \cdot)$ takes the same value on $Y_i$ and on the label of $k$. If the hash is mixed-modulus circular correlation robust, the scheme is private (prv.sim): the simulator, given the circuit's side information and the output $y$, outputs uniformly random projection-gate ciphertexts and input labels with decoding information consistent with $y$; when the correlation-robustness oracle is replaced by a random function the evaluator's real view is distributed exactly as the simulated one, so the prv.sim advantage is at most the correlation-robustness advantage of an explicit reduction.

## Proof sketch

Rewrite every label as the evaluator's active label plus a multiple of the offset. Each projection-gate ciphertext and each decoding entry then has the form $H(g, W^* + a\Delta_m) + c\Delta_{m'} + Q$ with $W^*$ and $Q$ known to the evaluator, and $c = 0$ whenever $a = 0$; the entries with $a \ne 0$ are oracle answers, which a random function makes uniform, and after that the wire values are needed only to shift the decoding information of the output wires, which the output determines.

## Depends on

- [Mixed-modulus circuits and BMR16 garbling](mixed-modulus-garbling.md)
- [Side-information functions and privacy notions for garbling schemes](../garbling-scheme-security/garbling-privacy-notions.md)

## Sources

- Marshall Ball, Tal Malkin and Mike Rosulek, "Garbling Gadgets for Boolean and Arithmetic Circuits", Proceedings of the 2016 ACM SIGSAC Conference on Computer and Communications Security, 2016.
