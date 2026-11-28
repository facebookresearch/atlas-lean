# External-memory BWT and LCP construction

Compressed indexes for large read collections rest on the multi-string Burrows–Wheeler transform and the LCP array. Both can be built by merging partial BWTs with sequential scans, and the resulting arrays support scan-based algorithms such as maximal-repeat detection.

- [Merging multi-string BWTs with LCP computation](merging-multi-string-bwts-with-lcp-computation.md)
- [Maximal repeats from a single scan of BWT and LCP](maximal-repeats-from-a-single-scan-of-bwt-and-lcp.md)
