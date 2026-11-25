# Verifiable secret sharing

A verifiable secret sharing protocol among $n$ parties, one of them the dealer, tolerating $t$ malicious parties, consists of a sharing phase and a reconstruction phase such that: (*commitment*) at the end of the sharing phase the views of the honest parties determine a value $s^*$ that the reconstruction phase outputs whatever the corrupted parties do, even if the dealer is corrupted; (*correctness*) if the dealer is honest then $s^*$ is the dealer's secret; and (*privacy*) if the dealer is honest then the joint view during the sharing phase of any coalition of at most $t$ corrupted parties, which does not include the dealer, is independent of the secret.

## Depends on

- [Security with abort against malicious adversaries](security-with-abort-against-malicious.md)

## Sources

- G. Asharov and Y. Lindell, "A full proof of the BGW protocol for perfectly secure multiparty computation", *Journal of Cryptology* 30(1):58–151, 2017; ePrint 2011/136, <https://eprint.iacr.org/2011/136>
- M. Ben-Or, S. Goldwasser and A. Wigderson, "Completeness theorems for non-cryptographic fault-tolerant distributed computation", *Proceedings of the 20th ACM STOC*, 1988
