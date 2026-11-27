# Crépeau's OT commitment realizes the ideal commitment functionality

In the ideal-OT hybrid model, Crépeau's commitment with $k$ transfers satisfies: (i) *correctness*: honest openings are accepted for every choice and mask vector; (ii) *equivocation against a corrupted receiver*: a simulator runs the commit phase without knowing $b$ and, upon learning $b$ at opening time, reconstructs the unique parity-correct pairs consistent with the receiver's recorded selections; the joint law of the opening, the receiver's transcript and its private state is identical to the real one; (iii) *extraction against a corrupted sender*: at the end of the commit phase, the strict majority of the parities of the sender's OT inputs (ties resolved to $0$) defines an extracted bit; an opening to the other bit is accepted for at most a $2^{-\lceil k/2\rceil}$ fraction of the receiver's hidden choices, so the real and simulated laws of the receiver's output and the sender's state can be coupled with disagreement probability at most $2^{-\lceil k/2 \rceil}$. Hence the protocol realizes the ideal commitment-with-abort functionality with statistical error $2^{-\lceil k/2\rceil}$.

## Proof sketch

An opening to the non-majority bit must flip the parity of at least $\lceil k/2\rceil$ pairs, and each flipped pair is caught unless the receiver's hidden choice selected the unchanged component, an independent event of probability $1/2$.

## Depends on

- [Crépeau's commitment from ideal oblivious transfer](commitment-from-oblivious-transfer.md)
- [The ideal commitment-with-abort functionality](ideal-commitment-functionality.md)

## Sources

- Ronald Cramer, "Introduction to Secure Computation", Revised version of the 1998 Aarhus Summer School lecture, 2000.
