# Sample Bounded With

`SampleBoundedWith cont s c`: along every path, the monadic computation `c` makes at most `s`
**sampling steps**; oracle queries are free (they are counted by `OracleBoundedWith`).
