# One-exchange ideal protocol

The trusted transition takes the API and backdoor inputs and
returns an API reply and a backdoor reply. The sole main party (role 2) forwards its API input
to the trusted box and its API output back to ID 0. The peer wire connects ID 1 directly to the
box. At the level of pairs of port values these are two identity tables, one on each side of
the transition. They cost two table lookups in the protocol, not in the simulator.

## Sources

- single-party specialization of R. Canetti, *Universally Composable Security: A Tutorial*, UC/EasyUC Summer School (2025), slides 25–26.
