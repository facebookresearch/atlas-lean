# Log Return

Log return of a gross return `G`: `Real.log G`. This is the shared
one-argument finance operation; `Domains.Economics.Finance.PortfolioLogReturn`
re-exports it. The definition is total: at a nonpositive gross return it is a
junk value, e.g. `logReturn 0 = Real.log 0 = 0`. A genuine log return requires
`0 < G`.
