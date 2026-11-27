# Robust hyperproperty preservation does not imply robust relational safety preservation

**Theorem (Abate, Blanco, Garg, Hriţcu, Patrignani and Thibault).** There is a compilation chain that satisfies [robust hyperproperty preservation](robust-hyperproperty-preservation.md)
but not robust 2-relational safety preservation, in the sense of [robust relational trace property preservation](robust-relational-trace-property-preservation.md).

In the witness the compiler is the identity and the target language adds a primitive with which the context reads the program's code as data. For one program a source
context can hard-code that program, which gives RHP, but no single source context reproduces target behaviour that distinguishes two programs by their code.

## Depends on

- [Robust hyperproperty preservation](robust-hyperproperty-preservation.md)
- [Robust relational trace property preservation](robust-relational-trace-property-preservation.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6 (numbering of this extended version, whose appendices are not in the proceedings), <https://arxiv.org/abs/1807.04603v6>: Section 4.3, Theorem 4.1 and its proof sketch.
