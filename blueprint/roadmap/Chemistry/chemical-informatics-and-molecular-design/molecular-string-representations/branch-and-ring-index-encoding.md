# Branch and ring index encoding

An active branch or ring symbol reads its argument from the symbols that follow it: each is mapped to a hexadecimal digit by a fixed table and the digits are read as one number. Missing symbols count as the digit zero, so a truncated string still yields an index.

Let $c$ map SELFIES symbols to $\{0, 1, \dots, 15\}$ by the source's fixed table (for instance $c([\mathrm{C}]) = 0$, $c([\mathrm{Ring1}]) = 1$, $c([\mathrm{Ring2}]) = 2$, $c([\mathrm{Branch1}]) = 3$, $c([=\mathrm{Branch1}]) = 4$, $c([\#\mathrm{Branch1}]) = 5$, $c([\mathrm{Branch2}]) = 6$, $c([=\mathrm{Branch2}]) = 7$, $c([\#\mathrm{Branch2}]) = 8$, $c([\mathrm{O}]) = 9$, $c([\mathrm{N}]) = 10$, $c([=\mathrm{N}]) = 11$, $c([=\mathrm{C}]) = 12$, $c([\#\mathrm{C}]) = 13$, $c([\mathrm{S}]) = 14$, $c([\mathrm{P}]) = 15$), every other symbol taking $c(s) = 0$. For a symbol carrying $\ell \in \{1,2,3\}$ that is *active*, the next $\ell$ symbols $s_1, \dots, s_\ell$ are popped in order of retrieval, $c_k = c(s_k)$, with missing digits set to $0$, and the index is

$$
N = 1 + \sum_{k=1}^{\ell} 16^{\,\ell-k} c_k \in \{1, \dots, 16^{\ell}\} .
$$

Activity is decided by the derivation state before any argument is read: a branch symbol met at $\mathbf{S}$ or at $\mathbf{X}_1$, and a ring symbol met at $\mathbf{S}$, are skipped without consuming arguments, so in `[Branch1][C]` at the start the following `[C]` is read as an atom symbol, not as a digit. For an active branch, $N$ bounds the symbols taken for the branch substring: the derivation consumes at most $N$ symbols, all of them when fewer remain, reserves $d_0 = \min(i-1, d(\beta))$ of the parent's budget and resumes the parent in $\mathbf{X}_{i-d_0}$. For an active ring symbol, $N$ counts back from the ring-initiating atom in derivation order, the first derived atom being used when fewer than $N$ atoms precede it.

A nonzero index does not mean a nonempty branch: with an exhausted queue the branch substring is empty and contributes nothing, and the source additionally flattens a branch that starts with a nested branch so that the emitted SMILES stays well formed.

## Depends on

- [The SELFIES chain-derivation grammar](selfies-derivation-grammar.md)

## Proof depends on

None.

## Expansion

A formal development fixes $c$ as a finite map with default zero, defines the pop-$\ell$ operation with zero padding, and defines $N$ by the display; $1 \le N \le 16^{\ell}$ follows from $0 \le c_k \le 15$ and $\sum_{k=1}^{\ell} 15 \cdot 16^{\ell-k} = 16^{\ell} - 1$. The stateful use is separate: a predicate deciding activity from the current nonterminal, the budget reservation, the bounded consumption and the parent restoration, each stated as part of the branch transition rather than of the index.

## Context

Undergraduate. A self-contained piece of the SELFIES specification; it is why arbitrary and even truncated symbol sequences still decode.

## Sources

- Alston Lo, Robert Pollice, AkshatKumar Nigam, Andrew D. White, Mario Krenn and Alán Aspuru-Guzik, *Recent advances in the Self-Referencing Embedded Strings (SELFIES) library*, Digital Discovery 2 (2023) 897–908, Section III D (Table III, Eqs. 16–17, and the note on flattening nested branches) and Section III E (ring symbols at the start symbol). DOI [10.1039/d3dd00044c](https://doi.org/10.1039/d3dd00044c), PMC10408573.
