# A fixed-length CRC frame parser recovers every encoded payload

Fix a monic polynomial $g$ over $\mathbb F_2$ of degree $r \ge 1$ and a payload length $l \ge 0$. The input is a finite
sequence of tokens $\mathsf{Start}$, $\mathsf{Bit}(b)$ with $b \in \{0, 1\}$, and $\mathsf{End}$. The fixed-length frame parser
is the sequential transducer whose states are $\mathsf{Idle}$ and $\mathsf{In}(k, S, w)$, with $k$ the number of body bits read,
$S$ the state of the [bit-serial CRC register](serial-crc-register-computes-the-remainder.md) of $g$ and $w$ the body bits read
so far. It starts in $\mathsf{Idle}$ and moves as follows:

- in $\mathsf{Idle}$, $\mathsf{Start}$ goes to $\mathsf{In}(0, 0, \varepsilon)$, while $\mathsf{Bit}(b)$ and $\mathsf{End}$
  output $\mathsf{reject}$ and stay in $\mathsf{Idle}$;
- in $\mathsf{In}(k, S, w)$, $\mathsf{Start}$ outputs $\mathsf{reject}$ and goes to $\mathsf{In}(0, 0, \varepsilon)$;
  $\mathsf{Bit}(b)$ goes to $\mathsf{In}(k + 1, (XS + b) \bmod g, wb)$ if $k < l + r$, and otherwise outputs
  $\mathsf{reject}$ and goes to $\mathsf{Idle}$; $\mathsf{End}$ outputs $\mathsf{accept}(w_0 \dots w_{l-1})$ if $k = l + r$ and
  $S = 0$, and otherwise outputs $\mathsf{reject}$, going to $\mathsf{Idle}$ in both cases;
- a frame still open when the input ends produces no output.

Then for every payload $p \in \{0, 1\}^l$, leading zeros included, the token sequence $\mathsf{Start}$, $\mathsf{Bit}(p_0), \dots,
\mathsf{Bit}(p_{l-1})$, $\mathsf{Bit}(q_0), \dots, \mathsf{Bit}(q_{r-1})$, $\mathsf{End}$, where $q_0 \dots q_{r-1}$ are the
CRC check bits of $p$, makes the parser output exactly $\mathsf{accept}(p)$, starting from and returning to $\mathsf{Idle}$.
The body has $l + r$ bits and its polynomial is the CRC encoding of $p$, which $g$ divides, so the register ends at $0$.

## Depends on

- [A bit-serial CRC register computes the remainder](serial-crc-register-computes-the-remainder.md)

## Sources

- A. S. Tanenbaum and D. J. Wetherall, *Computer Networks*, 5th edition, Pearson, 2011, Chapter 3 (framing and cyclic redundancy checks).
- W. W. Peterson and D. T. Brown, "Cyclic codes for error detection", *Proceedings of the IRE* 49(1):228–235, 1961.
