# The CRC frame parser rejects every frame hit by a short burst

Let $g$ be a monic polynomial over $\mathbb F_2$ of degree $r \ge 1$ with $g(0) = 1$, and run the
[fixed-length frame parser](fixed-length-crc-frame-parser-recovers-encoded-payloads.md) for $g$ and payload length $l$ from
$\mathsf{Idle}$. Take the frame $\mathsf{Start}$, $\mathsf{Bit}(c_0), \dots, \mathsf{Bit}(c_{l+r-1})$, $\mathsf{End}$ that
encodes a payload, and flip its body bits in the positions of a nonzero burst of length at most $r$ lying within the $l + r$
body positions, keeping the tokens $\mathsf{Start}$ and $\mathsf{End}$. Then the parser outputs $\mathsf{reject}$ for this frame
and accepts no payload from it, rather than accepting a different payload.

The corrupted body still has $l + r$ bits, so the parser reaches $\mathsf{End}$ with $k = l + r$, and its register state is the
corrupted body polynomial modulo $g$, which is nonzero because the
[serial check detects every short burst](serial-crc-check-detects-short-bursts.md).

## Depends on

- [A fixed-length CRC frame parser recovers every encoded payload](fixed-length-crc-frame-parser-recovers-encoded-payloads.md)
- [Burst errors](../cyclic-redundancy-checks/is-burst-le.md)

## Proof depends on

- [A bit-serial CRC check detects every short burst](serial-crc-check-detects-short-bursts.md)

## Sources

- A. S. Tanenbaum and D. J. Wetherall, *Computer Networks*, 5th edition, Pearson, 2011, Chapter 3 (framing and cyclic redundancy checks).
- W. W. Peterson and D. T. Brown, "Cyclic codes for error detection", *Proceedings of the IRE* 49(1):228–235, 1961.
