# Linear-memory hidden Markov model training

Baum–Welch training and Viterbi decoding of hidden Markov models on very long sequences without storing the $T\times N$ forward–backward trellis. Expected transition and emission counts can be accumulated in a single sweep by recurrences on weighted path sums, and scaling factors cancel in the re-estimation ratios.

- [Single-sweep expected-count recurrences for Baum–Welch](single-sweep-expected-count-recurrences-for-baum-welch.md)
