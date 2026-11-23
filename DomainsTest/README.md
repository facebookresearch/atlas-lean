# Domain model tests

Mirror the production module's path: `Domains/Transport/Accessibility.lean` is tested by `DomainsTest/Transport/Accessibility.lean`. Import the model from `Domains`, not from an old `MathlibExt` path. Tests may use its three foundation libraries but not other test libraries or `WantedExt`.

Run `lake build Domains DomainsTest` to compile the models and tests. Run `scripts/check.sh` for the repository checks, including the compiled dependency and axiom audit.
