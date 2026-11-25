# Security of Yao's garbled-circuit protocol against semi-honest adversaries

In Yao's protocol for a two-party functionality given by a Boolean circuit $C$, the garbler $P_1$ chooses two random labels for each wire, encodes each gate
as a garbled table whose rows encrypt the output-wire label under the pair of input-wire labels, and sends the garbled circuit with the labels of its
own input bits and decoding tables for the output wires. The evaluator $P_2$ obtains the labels of its input bits by oblivious transfer, evaluates the
garbled circuit gate by gate, and decodes the output. With point-and-permute, a pointer bit on each label selects the row to decrypt.

**Claim.** Evans, Kolesnikov and Rosulek argue, at an intuitive level, that if the oblivious transfer is secure against semi-honest adversaries and the garbled-row encryption is instantiated by a random oracle or a
pseudorandom function, then Yao's protocol securely computes $C$ against a semi-honest adversary corrupting either party. A corrupt garbler receives no messages
apart from the oblivious transfer. A corrupt evaluator never holds both labels of any wire: this holds for the input wires and inductively for every
gate, so apart from the output decoding the labels reveal nothing about the wire values.

## Depends on

- [Garbling schemes and Yao's construction](garbled-circuits-and-the-correctness-of-yao-s.md)
- [Two-party security against semi-honest adversaries](two-party-security-against-semi-honest.md)
- [Oblivious transfer from the decisional Diffie–Hellman assumption](oblivious-transfer-from-the-decisional.md)

## Expansion

This page becomes ready once:

- Security of the garbling scheme under a stated row-encryption assumption, and the simulation-based definition of semi-honest security for two-party protocols, with the simulators for both corrupted parties (statement prerequisites; not yet stated)

## Sources

- D. Evans, V. Kolesnikov and M. Rosulek, *A Pragmatic Introduction to Secure Multi-Party Computation*, Foundations and Trends in Privacy and Security 2(2–3), 2018, <https://securecomputation.org/docs/pragmaticmpc.pdf>: Section 3.1 (Figures 3.1–3.2, point-and-permute, the instantiation by a random oracle or a pseudorandom function, and the security argument for both corruptions).
