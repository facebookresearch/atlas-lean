# Correctness and privacy of BMR16 mixed-modulus garbling

BMR16 garbling of mixed-modulus circuits is correct: for every hash, tweak assignment, offsets $(\Delta_p)$ and zero labels, evaluating the garbled circuit on encoded inputs and decoding gives the circuit's output, so every garbled circuit the randomized garbler can output evaluates correctly on every input. The simulator, which outputs uniformly random projection-gate ciphertexts and decoding information consistent with the output $y$, produces views that always decode to $y$, and against a random function in place of the hash the real view of the evaluator is exactly the simulated one when distinct gates use distinct tweaks; hence the scheme is private (prv.sim) under mixed-modulus circular correlation robustness of the hash, with advantage at most the corresponding CCR advantage.

## Proof sketch

Each projection-gate ciphertext is masked by a hash value at an inactive label $x + c\Delta_p$ with $c \ne 0$ under a fresh tweak, which a random function makes uniform; linear gates reveal nothing beyond the active labels.

## Depends on

- [Mixed-modulus circuits and BMR16 garbling](mixed-modulus-garbling.md)
- [Side-information functions and privacy notions for garbling schemes](../garbling-scheme-security/garbling-privacy-notions.md)

## Sources

- Marshall Ball, Tal Malkin and Mike Rosulek, "Garbling Gadgets for Boolean and Arithmetic Circuits", Proceedings of the 2016 ACM SIGSAC Conference on Computer and Communications Security, 2016.
