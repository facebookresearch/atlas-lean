# Merge Hi Memcpy Temp To Data?

Forward bulk copy from temporary storage to distinct main data.  No raw
recursive temp-to-data memcpy helper exists below this tagged interface.  The
one-cell primitive is hardwired temporary-to-data and also models ordinary
`sortslice_copy`.
