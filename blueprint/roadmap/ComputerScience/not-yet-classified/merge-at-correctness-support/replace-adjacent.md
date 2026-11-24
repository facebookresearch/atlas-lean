# Replace Adjacent

Replace two adjacent correct pending runs by one correct stable merge.

The structural postcondition is supplied directly by
`mergeAt_preserves_pendingLayout`.  The two unchanged-run premises are the
precise frame obligations: they can be discharged with
`pendingRunOccurrenceKeys_eq_of_equalOutsideRange`.
