---
article_id: af_5cb2236aa1a4d0e3e205984d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.pPositions_unique
---

# Impartial Acyclic Game

The set of P-positions of a terminating impartial game is uniquely determined by stability
and absorption. N-positions are represented by the complement of the P-positions.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.GameTheory.ImpartialAcyclicGame](../../../sources/v2/MathlibExt.md)
- Antoine Renard and Michel Rigo, "Variants of Wythoff Game with Terminal Positions or Blocking Maneuvers," Journal of Integer Sequences 29 (2026), Article 26.1.6, Proposition (Folklore) (label pro:kernel), lines 438–448, https://cs.uwaterloo.ca/journals/JIS/VOL29/Rigo/rigo5.tex; stability and absorption are defined in lines 430–436. Termination is encoded by the well-foundedness of the move relation on the acyclic game graph. Proves `Wanted` entry `pPositions_unique`.
