# Crépeau's commitment from ideal oblivious transfer

To commit to a bit $b$ with security parameter $k$, the sender chooses $k$ independent uniform bits $r_1, \dots, r_k$ and offers the pairs $(r_j, r_j \oplus b)$ to $k$ ideal 1-out-of-2 oblivious transfers; the receiver selects with uniform private choices $s_j$ and records $r_j \oplus s_j b$. To open, the sender reveals $b$ and all pairs; the receiver accepts iff every pair has XOR equal to $b$ and agrees with the selected value. Hiding is perfect, since each selected value is a uniform bit whatever $b$.

## Depends on

- [Ideal 1-out-of-2, batched and 1-out-of-4 oblivious transfer](../../secure-multiparty-computation/oblivious-transfer-protocols/oblivious-transfer-functionalities.md)
- [The ideal commitment-with-abort functionality](ideal-commitment-functionality.md)

## Sources

- Ronald Cramer, "Introduction to Secure Computation", Revised version of the 1998 Aarhus Summer School lecture, 2000.
