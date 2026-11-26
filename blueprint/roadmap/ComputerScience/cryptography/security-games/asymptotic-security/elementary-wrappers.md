# Elementary wrappers

An interactive machine $B$ is an **elementary wrapper around $A$** if it can be structured as the composition $\langle M',A\rangle$ of an efficient interface $M'$ with one enclosed instance of $A$. The external environment interacts with $M'$; during an invocation $M'$ may communicate with $A$ and uses its replies to produce the external response. It is the interface, not the enclosed machine, that must satisfy the uniform overhead bound in the definition. In particular, when $A$ is efficient, the elementary wrapper around it is efficient.

## Depends on

- [Efficient interfaces](efficient-interfaces.md)
- [Efficient interactive machines](efficient-interactive-machines.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, September 2017, §2.4.3, Definition 2.12 and the ensuing discussion, pp. 33–34. <https://toc.cryptobook.us/>
